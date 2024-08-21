#!/usr/bin/env python3
from typing import Mapping, Set, TextIO

import os
import sys
import csv

# IT: Ugly hack; this can be avoided if we pull the script at the top level
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))
from clientlib.facts_to_cfg import Statement, Block, Function, construct_cfg, load_csv_map, load_csv_multimap # type: ignore

def emit(s: str, out: TextIO, indent: int=0):
    # 4 spaces
    INDENT_BASE = '    '

    print(f'{indent*INDENT_BASE}{s}', file=out)


def emit_stmt(stmt: Statement):
    def render_var(var: str):
        if var in tac_variable_value:
            return f"v{var.replace('0x', '')}({tac_variable_value[var]})"
        else:
            return f"v{var.replace('0x', '')}"

    defs = [render_var(v) for v in stmt.defs]
    uses = [render_var(v) for v in stmt.operands]

    if defs:
        print(f"{stmt.ident}: {', '.join(defs)} = {stmt.op} {', '.join(uses)}")
        #emit(f"{stmt.ident}: {', '.join(defs)} = {stmt.op} {', '.join(uses)}", out, 1)
    else:
        print(f"{stmt.ident}: {stmt.op} {', '.join(uses)}")
        #emit(f"{stmt.ident}: {stmt.op} {', '.join(uses)}", out, 1)


def pretty_print_block(block: Block, visited: Set[str], out: TextIO):
    emit(f"Begin block {block.ident}", out, 1)

    prev = [p.ident for p in block.predecessors]
    succ = [s.ident for s in block.successors]

    emit(f"prev=[{', '.join(prev)}], succ=[{', '.join(succ)}]", out, 1)
    emit(f"=================================", out, 1)

    for stmt in block.statements:
        emit_stmt(stmt, out)

    emit('', out)

    for block in block.successors:
        if block.ident not in visited:
            visited.add(block.ident)
            pretty_print_block(block, visited, out)


def pretty_print_tac(functions: Mapping[str, Function], out: TextIO):
    for function in sorted(functions.values(), key=lambda x: x.ident):
        visibility = 'public' if function.is_public else 'private'
        emit(f"function {function.name}({', '.join(function.formals)}) {visibility} {{", out)
        pretty_print_block(function.head_block, set(), out)

        emit("}", out)
        emit("", out)

#unused
def build_value_map(block):
    var_map = {}
    for stmt in block.statements:
        if stmt.op == 'CONST':
            continue
        if stmt.op == 'PHI':
            handle_phi_statement(stmt, block)
        else :
            def var_value(var: str):
                if var in tac_variable_value:
                    return f"{tac_variable_value[var]}"
                elif var in var_map:
                    return f"{var_map[var]}"
                else:
                    return f"v{var.replace('0x', '')}"
            uses = [var_value(v) for v in stmt.operands]
            var_map[stmt.defs[0]] = f"{stmt.op} {', '.join(uses)}"

# TODO: improve the heuristic to handle phi blocks
def phi_branch_heuristic(operands, block2):
    first = []
    second = []
    for operand in operands:
        a = operand.replace('V', '').replace('B', '').replace("S", '')
        b = block2.ident.replace('V', '').replace('B', '').replace("S", '')
        print(f"in handling phi, comparing: {a}, {b}")
        if len(a) == len(b):
            if a < b:
                first.append(operand)
            else:
                second.append(operand)
        elif len(a) < len(b):
            if a < b[-6:]:
                first.append(operand)
            else:
                second.append(operand)
        else:
            if a[0:6] < b:
                first.append(operand)
            else:
                second.append(operand)
    return first, second

# now only handle two predecessors / number of predecessors < number of phi operands
def handle_phi_statement(stmt, block:Block, f):
    preds = block.predecessors
    if len(preds) ==0:
        return stmt
    # TODO: Need to fix phi nodes for general cases
    if len(preds) != 2:
        return handle_phi_statement(stmt, preds[0], f)

    first = []
    second = []
    # heuristic to resolve operands
    if len(stmt.operands) == 2:
        first.append(stmt.operands[0])
        second.append(stmt.operands[1])
    else:
        first, second = phi_branch_heuristic(stmt.operands, preds[1])
    print(first, second)
    # fix resolving constraints
    first_val = []
    for var in first:
        print("trying to resolve var:", var)
        if var in tac_variable_value:
            first_val.append(f"const_{tac_variable_value[var]}")
        if var in load_storage_map.keys():
            print("find var in map", var)
            first_val.append("storage_"+load_storage_map[var])
        elif var.replace('V', 'S') in load_storage_map.keys():
            first_val.append("storage_"+load_storage_map[var.replace('V', 'S')])
        else:
            print("try resolve:", var)
            expr = resolve_val(var, preds[0], f)
            print(" resolve 1", expr)
            first_val.append(expr)
    second_val = []
    for var in second:
        print(var)
        if var in tac_variable_value:
            second_val.append(f"const_{tac_variable_value[var]}")
        elif var in load_storage_map.keys():
            second_val.append(load_storage_map[var])
        elif var.replace('V', 'S') in load_storage_map.keys():
            second_val.append("storage_"+load_storage_map[var.replace('V', 'S')])
        else:
            print("try resolve:", var)
            expr = resolve_val(var, preds[1], f)
            second_val.append(expr) 
            print("resolve 2", expr)  
    if len(first_val) == 0:
        return "(" + ' + '.join(second_val) + ")"
    elif len(second_val) == 0:
        return "(" + ' + '.join(first_val) + ")"
    
    print("now handling constraint: ", block.ident)
    last_statement = preds[0].statements[-1]
    current_block = preds[0]
    found = True
    c = None
    
    # Now only handle two predecessors. Trace back to previous jumpi
    # c is the constraint for branching and we assume the other block's constraint is (1-c)
    while last_statement.op != "JUMPI":
        if len(current_block.predecessors) >= 1:
            current_block = current_block.predecessors[0]
            last_statement = current_block.statements[-1]
        else:
            found = False
    if found:
        c = resolve_val( last_statement.operands[1],preds[0], f)
    
    # TODO: need to implement general cases
    return "{( " + ' OR '.join(first_val) + f" ) and [{c}] phi_OR [1 - {c}] and (" + ' OR '.join(second_val) + ")}"


def handle_var_from_phi(var, phi_stmt, block):
    a = var.replace('V', '').replace('B', '').replace("S", '')
    b = block.predecessors[1].ident.replace('V', '').replace('B', '').replace("S", '')
    print(f"in handling phi, comparing: {a}, {b}")
    if len(a) == len(b):
        if a < b:
            return 0
        else:
            return 1
    elif len(a) < len(b):
        if a < b[-6:]:
            return 0
        else:
            return 1
    else:
        if a[0:6] < b:
            return 0
        else:
            return 1          

# pretty printing for later evaluation
def pretty_print(op, operands):
    if op == "CALLDATALOAD":
        return f"CALLDATALOAD_{operands[0]}"        
    elif op in ["GT", "LT", "OR", "EQ", "ADD", "SUB", "MUL", "DIV"]:
        return f" ( {operands[0]} {op} {operands[1]} ) "
    # heuristic to get rid of AND 0xffff operand
    elif op == "AND":
        if operands[0].startswith("const_0x") and len(operands[0][8:]) == operands[0].count("f"):
            return f" {operands[1]} "
        elif operands[1].startswith("const_0x") and len(operands[1][8:]) == operands[1].count("f"):
            return f" {operands[0]} "
        else:
            return f" ( {operands[0]} {op} {operands[1]} ) "
    else:
        return " ( " + op + " "+ ",".join(operands) + " ) "   

def resolve_val(var, block, f):
    # check if the value of the var is already known
    if var in tac_variable_value:
        return f"const_{tac_variable_value[var]}"
    elif var in load_storage_map.keys():
        return "storage_"+load_storage_map[var]
    elif var.replace('V', 'S') in load_storage_map.keys():
        return "storage_"+load_storage_map[var.replace('V', 'S')]
    
    print("============================\n resolving: ", var, block.ident)
    stmt_reverse = block.statements[::-1]
    #unknown_var= [var,]
    unknown_var = []
    expr = var
    value_map = {}

    #bottom up approach
    for stmt in stmt_reverse:
        emit_stmt(stmt)
        if stmt.op == 'JUMPI':
            continue
            # only handle block constraint for phi nodes
            '''
            if stmt.operands[1] == var:
                continue
            else:
                print("resolving block constraint") 
                block_constraint = resolve_val(stmt.operands[1], block)
                print("Done resolving block constraint") 
                continue
            '''
        elif 'MLOAD' in stmt.op:
            expr = expr.replace(stmt.defs[0], "MLOAD_"+stmt.operands[0])
            try:
                unknown_var.remove(stmt.defs[0])
            except ValueError:
                print("not exist")
            emit("encounter MLOAD, constraint may not be complete.", f)
            continue
        elif 'MSTORE' in stmt.op:
            emit("encounter MSTORE, constraint may not be complete.", f)
            continue
        elif stmt.op == 'SSTORE':
            emit("encounter SSTORE, constraint may not be complete.", f)
            continue
        elif stmt.op == 'CONST':
            continue
        elif stmt.op == 'PHI':
            if stmt.defs[0] not in expr:
                continue
                for variable in stmt.operands:
                    if variable in expr and variable != expr:
                        pre_idx = handle_var_from_phi(variable, stmt, block)
                        variable_expr = resolve_val(variable, block.predecessors[pre_idx], f)
                        expr = expr.replace(variable, variable_expr) 
            else:
                if "MLOAD"+stmt.defs[0] in expr:
                    continue
                print("handling phi", expr)
                val = handle_phi_statement(stmt, block, f)
                #value_map[stmt.defs[0]] = handle_phi_statement(stmt, block)
                print("after handle phi: ", expr, val)
                expr = expr.replace(stmt.defs[0], val)
                print("replaced handle phi: ", expr)
        elif stmt.op == "JUMP":
            continue
        else:
            if stmt.defs[0] not in expr:
                continue
            if stmt.op == 'CALLPRIVATE':
                expr = expr.replace(stmt.defs[0], "CALLPRIVATE")
                emit("encounter PRIVATE CALL, constraint may not be complete.", f)
                continue
            if stmt.op == 'STATICCALL':
                expr = expr.replace(stmt.defs[0], "CALLPRIVATE")
                emit("encounter STATIC CALL, constraint may not be complete.", f)
                continue
            print("regular op", stmt.op)
            def calc_var(var: str, unknown_var, sym):
                print("operands :", var)
                if var in tac_variable_value:
                    print("case 1")
                    return f"const_{tac_variable_value[var]}"
                elif var in load_storage_map.keys():
                    print("case 2a")
                    return "storage_"+load_storage_map[var]
                elif var.replace('V', 'S') in load_storage_map.keys():
                    print("case 2b")
                    return "storage_"+load_storage_map[var.replace('V', 'S')]
                else:
                    print("case 3")
                    if sym in expr:
                        unknown_var.append(var)
                    return f"{var}"
            operands = [calc_var(v, unknown_var, stmt.defs[0]) for v in stmt.operands]
            value_map[stmt.defs[0]] = pretty_print(stmt.op, operands)
            print(f"trying to remove {stmt.defs[0]} from {unknown_var}")
            try:
                unknown_var.remove(stmt.defs[0])
            except ValueError:
                print("not exist")
            print(expr)
            print("couple:", stmt.defs[0], value_map[stmt.defs[0]])
            expr = expr.replace(stmt.defs[0], value_map[stmt.defs[0]])
            print("after replace: ",expr)
            
    # no definition was found for the unsolved value in the current block     
    if var == expr:
        unknown_var.append(var)
    print("finished processing block: ", block.ident)
    print("list of variables unsolved: ", unknown_var)
    for uvar in unknown_var:
        if uvar in statement_variable_list.keys():
            print("uvar in statement-variable list")
            val = resolve_val(uvar, blocks[statement_variable_list[uvar]], f)
            expr = expr.replace(uvar, val)
        elif '_' in uvar and uvar.find('_') != -1:
            print("removing underscore from uvar")
            uvar1 = uvar[:uvar.find('_')]
            if uvar1 in statement_variable_list.keys():
                val = resolve_val(uvar, blocks[statement_variable_list[uvar1]], f)
                expr = expr.replace(uvar, val)
            else:
                for pre_bl in block.predecessors:
                    print(f"{expr} recursion with {uvar} {block.ident} {pre_bl.ident}")
                    val = resolve_val(uvar, pre_bl, f) 
                    expr = expr.replace(uvar, val)
        else:
            for pre_bl in block.predecessors:
                print(f"{expr} recursion with {uvar} {block.ident} {pre_bl.ident}")
                val = resolve_val(uvar, pre_bl, f) 
                expr = expr.replace(uvar, val)
    return expr

######################################################################
# StorageInitRevertCheck.csv
# row0                   row1         row2             row3
# revert statement      storage_loc   loadstatement    revertblock
#######################################################################

def load_csv_storage_revert(path):
    # Load the CSV file with space separator
    with open(path, mode='r') as file:
        csv_reader = csv.reader(file, delimiter='\t')
        revert_block_list = []    
        # Iterate over each row in the CSV file
        for row in csv_reader:
            revert_block_list.append(row[3])
        return set(revert_block_list)
    
def get_load_storage_map(path):
    with open(path, mode='r') as file:
        csv_reader = csv.reader(file, delimiter='\t')
        # map from load statement to  loc
        ret_map = {}
        for row in csv_reader:
            if row[2] in ret_map:
                continue
            else:
                ret_map[row[2]] = row[1]        
        return ret_map

def main():
    global tac_variable_value, statement_variable_list, load_storage_map, blocks
    # replace bytecode here
    with open('../bytecode.hex', 'r') as file:
        runtime = file.read().rstrip()
    code = bytes.fromhex(runtime)
    tac_variable_value = load_csv_map('TAC_Variable_Value.csv')
    statement_variable_list = load_csv_map('TAC_OriginalStatement_Block.csv')
    blocks, _  = construct_cfg()
    
    rb_list = load_csv_storage_revert('StorageInitRevertCheck.csv')
    load_storage_map = get_load_storage_map('StorageInitRevertCheck.csv')
    
    with open('revert-constraint.log', 'w') as f:
        for block_id in rb_list:
            emit(f"{block_id}", f)
            # revert block can only have one predecessor
            block_pred = blocks[block_id].predecessors[0]
            
            # extract the condition variable:
            last_statement = block_pred.statements[-1]
            condition_var = last_statement.operands[1]
            print(condition_var)
            try:
                expr = resolve_val(condition_var, block_pred, f)
                emit(f"constraint: {expr}", f)
            except:
                print("Encountered Error")
            def render_var(var: str):
                if var in tac_variable_value:
                    return f"{tac_variable_value[var]}"
                else:
                    return f"v{var.replace('0x', '')}"

            stmts = blocks[block_id].statements
            found_error_message = False
            error_message = ''
            for stmt in stmts:
                # two heuristic to handle error messages
                if stmt.op == "CODECOPY":
                    uses = [render_var(v) for v in stmt.operands]
                    error_message = code[int(uses[1],16): int(uses[1],16) + int(uses[2],16)]
                    error_message = bytes([byte for byte in error_message if byte != 0]).decode("utf-8")
                    found_error_message = True
                    break
                if stmt.op == "MSTORE" and stmt.operands[1] in tac_variable_value:
                    print(tac_variable_value[stmt.operands[1]], tac_variable_value[stmt.operands[1]].startswith('0x8c379a'))
                    # heuristic to extract error message
                    if not tac_variable_value[stmt.operands[1]].startswith('0x8c379a') and len(tac_variable_value[stmt.operands[1]])>4:
                        temp = bytes(bytes.fromhex(tac_variable_value[stmt.operands[1]][2:]))
                        temp = bytes([byte for byte in temp if byte != 0])
                        error_message = error_message +  temp.decode("utf-8")
                        print(error_message)
                        found_error_message = True
            if not found_error_message:
                emit("No error message or unhandled for now", f)
            else:
                emit(f"message:{error_message}", f)
            emit("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n", f)
        emit("Analysis Completed.", f)

if __name__ == "__main__":
    main()
