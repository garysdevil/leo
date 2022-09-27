// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the Leo library.

// The Leo library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The Leo library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the Leo library. If not, see <https://www.gnu.org/licenses/>.

use crate::StaticSingleAssigner;

use leo_ast::{Block, Finalize, Function, FunctionConsumer, Program, ProgramConsumer, StatementConsumer};

impl FunctionConsumer for StaticSingleAssigner<'_> {
    type Output = Function;

    /// Reconstructs the `Function`s in the `Program`, while allocating the appropriate `RenameTable`s.
    fn consume_function(&mut self, function: Function) -> Self::Output {
        // Allocate a `RenameTable` for the function.
        self.push();

        // There is no need to reconstruct `function.inputs`.
        // However, for each input, we must add each symbol to the rename table.
        for input_variable in function.input.iter() {
            self.rename_table
                .update(input_variable.identifier().name, input_variable.identifier().name);
        }

        let block = Block {
            span: function.block.span,
            statements: self.consume_block(function.block),
        };

        // Remove the `RenameTable` for the function.
        self.pop();

        let finalize = function.finalize.map(|finalize| {
            // Allocate a `RenameTable` for the finalize block.
            self.push();

            // There is no need to reconstruct `finalize.inputs`.
            // However, for each input, we must add each symbol to the rename table.
            for input_variable in finalize.input.iter() {
                self.rename_table
                    .update(input_variable.identifier().name, input_variable.identifier().name);
            }

            let block = Block {
                span: finalize.block.span,
                statements: self.consume_block(finalize.block),
            };

            // Remove the `RenameTable` for the finalize block.
            self.pop();

            Finalize {
                identifier: finalize.identifier,
                input: finalize.input,
                output: finalize.output,
                output_type: finalize.output_type,
                block,
                span: finalize.span,
            }
        });

        Function {
            annotations: function.annotations,
            identifier: function.identifier,
            input: function.input,
            output: function.output,
            output_type: function.output_type,
            block,
            finalize,
            span: function.span,
        }
    }
}

impl ProgramConsumer for StaticSingleAssigner<'_> {
    type Output = Program;

    fn consume_program(&mut self, input: Program) -> Self::Output {
        Program {
            name: input.name,
            network: input.network,
            expected_input: input.expected_input,
            // TODO: Do inputs need to be processed? They are not processed in the existing compiler.
            imports: input
                .imports
                .into_iter()
                .map(|(name, import)| (name, self.consume_program(import)))
                .collect(),
            functions: input
                .functions
                .into_iter()
                .map(|(i, f)| (i, self.consume_function(f)))
                .collect(),
            circuits: input.circuits,
            mappings: input.mappings,
        }
    }
}
