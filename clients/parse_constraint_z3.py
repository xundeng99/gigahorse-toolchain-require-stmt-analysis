from web3 import Web3
import re
from z3 import *
import time

def query(storage_slot, idx_s = 0, idx_e = -1):
    client = Web3(Web3.HTTPProvider("http://127.0.0.1:8536/"))
    storage_value = client.eth.get_storage_at(contract_address, storage_slot, block_identifier=block_number)
    #print(f'Storage at slot {storage_slot} at block {block_number}: {storage_value.hex()}')
    revert = storage_value[::-1]
    #idx_e = idx_e + 1
    tmp = revert[idx_s:idx_e+1][::-1]
    return tmp.hex()

def extract_var(cs):
    var = []
    tokens = cs.split()
    storage_map = {}
    for token in tokens:
        if token in ['(', ')']:
            continue
        if token.startswith("storage"):
            parts = token.split('_')
            if len(parts) == 4:
                storage_map[token] = query(parts[1], int(parts[2]), int(parts[3]))
            else:
                storage_map[token] = query(parts[1])
        if token.startswith("const"):
            continue
        if token == 'ADDRESS':
            continue
        if token == "EXTCODE":
            continue
        if token.startswith("CALLDATALOAD"):
            if token not in var:
                var.append(token)
        if "arg" in token:
            if token not in var:
                var.append(token)
    return var, storage_map

#TODO: Add support for other variables
def no_var_in_cs(cs):
    return "CALLER" not in cs and "EXTCODE" not in cs and "ADDRESS" not in cs and "CALLDATALOAD" not in cs and "NONNEGCODE" not in cs

def evaluate(before, after):
    for item in before:
        ms = item["message"]
        cs = item["c"]
        for item1 in after:
            ms1 = item1["message"]
            cs1 = item1["c"]
            if ms1 == ms:
                print("========================================================")
                if cs == cs1:
                    print("Constraint equivalent True.")
                    print("Before: ", cs)
                    print("After: ", cs1)
                    print(ms) 
                # If there is no variables in the constraint directly 
                elif no_var_in_cs(cs) and no_var_in_cs(cs1):
                    if eval(cs) != eval(cs1):
                        print("Constraint equivalent False.")
                        print("Before: ", cs)
                        print("After: ", cs1)
                        print(ms)
                    else:
                        print("Constraint equivalent True.")
                        print("Before: ", cs)
                        print("After: ", cs1)
                        print(ms) 
                else:
                    var_string = ""
                    z3_script ="""print("invoking z3.")\nCALLER = BitVec('CALLER', 160)\nADDRESS = BitVec('ADDRESS', 160)\nNONNEGCODESIZE = Bool('NONNEGCODESIZE')\n"""
                    for var in var_set:
                        z3_script  = z3_script + f"{var} = INT({var})\n" 
                        var_string  = var_string + f"{var}, "
                    z3_script  = z3_script + f"expr1 = {cs}\nexpr2 = {cs1}\nsolver = Solver()\n" 
                    z3_script  = z3_script + f"solver.add(ForAll([{var_string} CALLER, ADDRESS, NONNEGCODESIZE], expr1 == expr2))\n"
                    z3_script = z3_script + """if solver.check() == sat:\n    print("Constraints Equivalent True.")\nelse:    print("Constraints Equivalent False.")\n"""
                    exec(z3_script)
                    print("Before: ", cs)
                    print("After: ", cs1)
                    print(ms)
                    
def simple_parsing(cs):
    cs = cs.replace("[", " ( ")
    cs = cs.replace("]", " ) ")
    cs = cs.replace("{", " ( ")
    cs = cs.replace("}", " ) ")
    cs = cs.replace("ISZERO", "0 == ")
    cs = cs.replace("phi_OR", " || ")
    cs = cs.replace("OR", " || ")
    cs = cs.replace("EQ", " == ")
    #hack to avoid replacing ADDRESS-> + RESS
    cs = cs.replace("ADDRESS", "address")
    cs = cs.replace("ADD", " + ")
    cs = cs.replace("address", "ADDRESS")
    cs = cs.replace("AND", " && ")
    cs = cs.replace("SUB", " - ")
    cs = cs.replace("DIV", " / ")
    cs = cs.replace("MUL", " * ")
    
    return cs

def pre_evaluate(before):
    message_dict = []
    for item in before:
        ms = item["message"]
        cs = item["constraint"]
        cs = simple_parsing(cs)
        vars, storage_map = extract_var(cs)
        for item in storage_map.keys():
            cs = cs.replace(item, storage_map[item])
        cs = cs.replace("const_", "")
        #if no_var_in_cs(cs):
        #    message_dict.append({"message":ms, "c":eval(cs)})
        #else:
        cs = cs.replace("0 ==   ( EXTCODESIZE  ( ADDRESS  )  )", "NONNEGCODESIZE")
        message_dict.append({"message":ms, "c":cs})
    return message_dict, vars

def parse_constraints(file_content):
    # Split the file content into sections by the delimiter
    sections = file_content.strip().split("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
    
    parsed_data = []
    
    # Regular expressions to match the constraint and message
    constraint_pattern = r"constraint:\s*(.*)"
    message_pattern = r"message:(.*)"
    incomplete_pattern = r"encounter (.*) constraint may not be complete."

    for section in sections:
        #print(section.strip())
        if section.strip():
            incomplete_match = re.match(incomplete_pattern, section.strip())
            if incomplete_match:
                continue

            # Extract the address (first line in each section)
            address_match = re.match(r"0x[0-9a-fA-F]+", section.strip())
            address = address_match.group(0) if address_match else None
            # Extract the constraint
            constraint_match = re.search(constraint_pattern, section)
            constraint = constraint_match.group(1).strip() if constraint_match else None
            
            # Extract the message
            message_match = re.search(message_pattern, section)
            message = message_match.group(1).strip() if message_match else None

            if constraint is None: 
                continue 
            # some senarios to skip
            if "CALLPRIVATE" in constraint:
                continue
            # Skip no error message entries
            if "no error message" in message:
                continue
            if "SafeMath" in message:
                continue
            
            #print(address, constraint, message)
            #Ignoring the block_id (address) information
            parsed_data.append({
                #"address": address,
                "constraint": constraint,
                "message": message
            })
    return parsed_data

def remove_duplicates(dict_list):
    # Create an empty set to track seen dictionaries
    seen = set()
    unique_list = []
    
    for d in dict_list:
        # Convert the dictionary to a frozenset of its items to make it hashable
        # frozenset ensures that the order of items doesn't matter
        dict_items = frozenset(d.items())
        
        # If this frozenset is not in seen, add it to the result and seen
        if dict_items not in seen:
            seen.add(dict_items)
            unique_list.append(d)
    
    return unique_list

def main():
    global contract_address, block_number, var_set
    time_start = time.time()
    client = Web3(Web3.HTTPProvider("http://127.0.0.1:8536/"))
    contract_address = '0x244cf1DEF777a5030B93516fC74FC081221c1Ad6'
    block_number = 15455180
    before_log_path = './before.log'
    after_log_path = './after.log'
    before_log_content = ''
    after_log_content = ''
    with open(before_log_path, 'r') as file:
        before_log_content = file.read()
    with open(after_log_path, 'r') as file:
        after_log_content = file.read()
    constraint_b =  parse_constraints(before_log_content)
    constraint_b = remove_duplicates(constraint_b)
    constraint_a = parse_constraints(after_log_content)
    constraint_a = remove_duplicates(constraint_a)
    # perform simple parsing and rpc storage slot
    before, before_vars = pre_evaluate(constraint_b)
    after, after_vars = pre_evaluate(constraint_a)
    var_set = set(before_vars + after_vars)
    # prove equivalence
    evaluate(before, after)
    time_end = time.time()
    print("Time Elapsed: ",time_end - time_start)
    
if __name__ == '__main__':
    main()
