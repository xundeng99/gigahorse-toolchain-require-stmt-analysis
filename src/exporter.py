"""exporter.py: abstract classes for exporting facts"""

import abc
import csv
import os
import src.opcodes as opcodes
import src.basicblock as basicblock
from src.common import public_function_signature_filename, event_signature_filename, error_signature_filename


from typing import List, Tuple, Dict, Any, Optional

opcode_output = {'alters_flow':bool, 'halts':bool, 'is_arithmetic':bool,
                 'is_call':bool, 'is_dup':bool, 'is_invalid':bool,
                 'is_log':bool, 'is_memory':bool, 'is_missing':bool,
                 'is_push':bool, 'is_storage':bool, 'is_swap':bool,
                 'log_len':int, 'possibly_halts':bool, 'push_len':int,
                 'stack_delta':int, 'pop_words':int, 'push_words':int,
                 'gas': int, 'ord':int
}    

def generate_interface():
    f = open('logic/decompiler_input_statements.dl', 'w')
    f.write('// Fact loader. This file was generated by bin/generatefacts, do not edit\n\n')
    
    for opname, opcode in opcodes.OPCODES.items():
        if opcode.is_push():
            f.write(f'.decl {opname}(stmt: Statement, value: Value)\n')
            f.write(f'{opname}(stmt, value) :- Statement_Opcode(stmt, "{opname}"), PushValue(stmt, value).\n')
        else:
            f.write(f'.decl {opname}(stmt: Statement)\n')
            f.write(f'{opname}(stmt) :- Statement_Opcode(stmt, "{opname}").\n')
        f.write('\n')
    f.close()
    f = open('logic/decompiler_input_opcodes.dl', 'w')
    f.write('// Static opcode data. This file was generated by bin/generatefacts, do not edit\n\n')
    for prop, typ in opcode_output.items():
        relname = ''.join(map(lambda a : a[0].upper()+ a[1:], ('opcode_'+prop).split('_')))
        if typ == bool:
            f.write(f'.decl {relname}(instruction: Opcode)\n')
            f.write(f'{relname}(instruction) :- {relname}(instruction).\n')
        elif typ == int:
            f.write(f'.decl {relname}(instruction: Opcode, n: number)\n')
            f.write(f'{relname}(instruction, n) :- {relname}(instruction, n).\n')
        else:
            raise NotImplementedError('Unknown: '+str(typ))
      
        f.write('\n')

    opcode_key = 'name'
    for prop, typ in opcode_output.items():
        relname = ''.join(map(lambda a : a[0].upper()+ a[1:], ('opcode_'+prop).split('_')))
        opcode_property = []
        for k, opcode in opcodes.OPCODES.items():
            prop_val = getattr(opcode, prop)()
            if typ == bool and prop_val:
                f.write(f'{relname}("{getattr(opcode, opcode_key)}").\n')
            elif typ == int:
                f.write(f'{relname}("{getattr(opcode, opcode_key)}", {prop_val}).\n')
        f.write('\n')
    f.close()

def get_disassembly(statement_opcode, push_value):
    output = []
    row_format ="{:>7}: {:<10}"
    for s, op in statement_opcode:
        row = row_format.format(s, op)
        if s in push_value:
            row += push_value[s]
        output.append(row)
    return '\n'.join(output)            


class Exporter(abc.ABC):
    def __init__(self, output_dir: str):
        """
        Args:
          output_dir: directory to store facts
        """
        self.output_dir = output_dir

    @abc.abstractmethod
    def export(self):
        """
        Exports the source object to an implementation-specific format.
        """

class TsvExporter(Exporter):
    def __init__(self, output_dir: str):
        super().__init__(output_dir)

    def get_out_file_path(self, filename):
        return os.path.join(self.output_dir, filename)

    def generate(self, filename: str, entries: List[Any]):
        with open(self.get_out_file_path(filename), 'w') as f:
            writer = csv.writer(f, delimiter='\t', lineterminator='\n')
            writer.writerows(entries)


class InstructionTsvExporter(TsvExporter):
    """
    Prints a textual representation of the given CFG to stdout.

    Args:
      blocks: low-level evm block representation to be output
      ordered: if True (default), print BasicBlocks in order of entry
      bytecode_hex: bytecode in hexadecimal form, used to export the compiler metadata
      metadata: dict containing metadata output by the solidity compiler
    """

    def __init__(self, output_dir: str, blocks: List[basicblock.EVMBasicBlock], ordered: bool = True,
                 bytecode_hex: Optional[str] = None, metadata: Optional[Dict[Any, Any]] = None):
        super().__init__(output_dir)
        self.blocks = blocks
        self.ordered = ordered
        self.bytecode_hex = bytecode_hex
        self.process_metadata(metadata)

    def process_metadata(self, metadata: Optional[Dict[Any, Any]] = None) -> None:
        """
        Processes metadata dicts are produced by solc, to lists of facts we can output
        """
        def process_function_debug_data(function_debug_data: Dict[str, Dict[str, Optional[int]]]) -> List[Tuple[str, str, int, int]]:
            return [(function_id,
                    hex(debug_info["entryPoint"]) if debug_info["entryPoint"] else "0x0",
                    debug_info["parameterSlots"] if debug_info["parameterSlots"] else 0,
                    debug_info["returnSlots"]if debug_info["returnSlots"] else 0)
                for function_id, debug_info in function_debug_data.items()]

        def process_immutable_refs(immutable_refs: Dict[str, List[Dict[str, int]]]) -> List[Tuple[str, int]]:
            res = []
            for id, accesses in immutable_refs.items():
                for access in accesses:
                    res.append((hex(access['start']), int(id)))
            return res

        self.function_debug_data = process_function_debug_data(metadata.get('function_debug_info', {})) if metadata is not None else []
        self.immutable_references = process_immutable_refs(metadata.get('immutable_references', {})) if metadata is not None else []

    def export(self):
        """
        Print basic block info to tsv.
        """

        def get_version_str(metadata_prefix):
            index = self.bytecode_hex.rindex(metadata_prefix) + len(metadata_prefix)
            version_bytes = self.bytecode_hex[index : index + 6]
            return f"{int(version_bytes[0:2], 16)}.{int(version_bytes[2:4], 16)}.{int(version_bytes[4:6], 16)}"

        def link_or_output_signature_file(signatures_filename_in: str, signatures_filename_out_simple: str):
            signatures_filename_out = self.get_out_file_path(signatures_filename_out_simple)
            if os.path.isfile(signatures_filename_in):
                try:
                    os.symlink(signatures_filename_in, signatures_filename_out)
                except FileExistsError:
                    pass
            else:
                open(signatures_filename_out, 'w').close()

        if self.output_dir != "":
            os.makedirs(self.output_dir, exist_ok=True)
        
        if self.bytecode_hex:
            with open(self.output_dir + "/bytecode.hex", "w") as f:
                assert '\n' not in self.bytecode_hex
                f.write(self.bytecode_hex)

            # 0x64 + "solc" + 0x43 which is followed by the solc version
            # only exists in solidity bytecode compiled using solc >= 0.5.9 when it is not explicitly removed
            solidity_metadata_prefix = b"\x64solc\x43".hex()
            # 0xa165 + "bzzr0" is followed by the swarn hash of the metadata file (useless to us)
            # Was introduced in solc 0.4.7 and changed in 0.5.9
            solidity_metadata_prefix_old = b"\xa1\x65bzzr0".hex()
            # 0xa165 + "vyper" + 0x83 which is followed by the vyper version
            # works for vyper versions >= 0.3.4 (followed by the bytecode length for versions >= 0.3.5)
            vyper_metadata_prefix = b"\xa1\x65vyper\x83".hex()

            language = "unknown"
            compiler_version = "unknown"

            if solidity_metadata_prefix in self.bytecode_hex:
                language = "solidity"
                compiler_version = get_version_str(solidity_metadata_prefix)
            elif solidity_metadata_prefix_old in self.bytecode_hex:
                language = "solidity"
                compiler_version = "0.4.7<=v<0.5.9"
            elif vyper_metadata_prefix in self.bytecode_hex:
                language = "vyper"
                compiler_version = get_version_str(vyper_metadata_prefix)

            with open(self.output_dir + "/compiler_info.csv", "w") as f:
                f.write(f"{language}\t{compiler_version}")

        link_or_output_signature_file(public_function_signature_filename, 'PublicFunctionSignature.facts')
        link_or_output_signature_file(event_signature_filename, 'EventSignature.facts')
        link_or_output_signature_file(error_signature_filename, 'ErrorSignature.facts')
        
        instructions = []
        instructions_order = []
        push_value = []
        for block in self.blocks:
            for op in block.evm_ops:
                instructions_order.append(int(op.pc))
                instructions.append((hex(op.pc), op.opcode.name))
                if op.opcode.is_push():
                    push_value.append((hex(op.pc), hex(op.value)))

        instructions_order = list(map(hex, sorted(instructions_order)))
        self.generate('Statement_Next.facts', zip(instructions_order, instructions_order[1:]))

        self.generate('Statement_Opcode.facts', instructions)
                    
        self.generate('PushValue.facts', push_value)
        dasm = get_disassembly(instructions, dict(push_value))
        with open(self.get_out_file_path('contract.dasm'), 'w') as f:
            f.write(dasm)

        self.generate('HighLevelFunctionInfo.facts', self.function_debug_data)
        self.generate('ImmutableLoads.facts', self.immutable_references)
