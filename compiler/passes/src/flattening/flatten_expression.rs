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

use crate::Flattener;
use itertools::Itertools;

use leo_ast::{
    AccessExpression, AssociatedFunction, Circuit, CircuitExpression, CircuitMember, CircuitVariableInitializer,
    Expression, ExpressionReconstructor, MemberAccess, Statement, TernaryExpression, TupleExpression,
};

// TODO: Clean up logic. To be done in a follow-up PR (feat/tuples)

impl ExpressionReconstructor for Flattener<'_> {
    type AdditionalOutput = Vec<Statement>;

    /// Replaces a tuple access expression with the appropriate expression.
    fn reconstruct_access(&mut self, input: AccessExpression) -> (Expression, Self::AdditionalOutput) {
        let mut statements = Vec::new();
        (
            match input {
                AccessExpression::AssociatedFunction(function) => {
                    Expression::Access(AccessExpression::AssociatedFunction(AssociatedFunction {
                        ty: function.ty,
                        name: function.name,
                        args: function
                            .args
                            .into_iter()
                            .map(|arg| self.reconstruct_expression(arg).0)
                            .collect(),
                        span: function.span,
                    }))
                }
                AccessExpression::Member(member) => Expression::Access(AccessExpression::Member(MemberAccess {
                    inner: Box::new(self.reconstruct_expression(*member.inner).0),
                    name: member.name,
                    span: member.span,
                })),
                AccessExpression::Tuple(tuple) => {
                    // Reconstruct the tuple expression.
                    let (expr, stmts) = self.reconstruct_expression(*tuple.tuple);

                    // Accumulate any statements produced.
                    statements.extend(stmts);

                    // Lookup the expression in the tuple map.
                    match expr {
                        Expression::Identifier(identifier) => {
                            // Note that this unwrap is safe since TYC guarantees that all tuples are declared and indices are valid.
                            // In this pass, we add all tuple assignments to `self.tuples`.
                            self.tuples.get(&identifier.name).unwrap()[tuple.index.to_usize()].clone()
                        }
                        _ => unreachable!("SSA guarantees that subexpressions are identifiers or literals."),
                    }
                }
                expr => Expression::Access(expr),
            },
            statements,
        )
    }

    /// Reconstructs a circuit init expression, flattening any tuples in the expression.
    fn reconstruct_circuit_init(&mut self, input: CircuitExpression) -> (Expression, Self::AdditionalOutput) {
        let mut statements = Vec::new();
        let mut flattened_expressions = Vec::with_capacity(input.members.len());

        // Reconstruct and flatten the argument expressions.
        for member in input.members.into_iter() {
            // Note that this unwrap is safe since SSA guarantees that all circuit variable initializers are of the form `<name>: <expr>`.
            let (expr, stmts) = self.reconstruct_expression(member.expression.unwrap());
            // Accumulate any statements produced.
            statements.extend(stmts);
            // Flatten the expression.
            flattened_expressions.extend(self.flatten_subexpression(expr));
        }

        // Lookup the flattened definition of the circuit.
        // Note that this unwrap is safe since TYC guarantees that all circuits are declared.
        let circuit: &Circuit = self.flattened_circuits.get(&input.name.name).unwrap();

        // Collect the names of the flattened circuit members.
        let names = circuit
            .members
            .iter()
            .map(|CircuitMember::CircuitVariable(identifier, _)| identifier)
            .cloned();

        let flattened_members = names
            .zip_eq(flattened_expressions)
            .map(|(identifier, expression)| CircuitVariableInitializer {
                identifier,
                expression: Some(expression),
            })
            .collect();

        (
            Expression::Circuit(CircuitExpression {
                name: input.name,
                members: flattened_members,
                span: input.span,
            }),
            statements,
        )
    }

    // TODO: Document reduction of nested tuples
    /// Reconstructs ternary expressions over tuples and circuits, accumulating any statements that are generated.
    /// This is necessary because Aleo instructions does not support ternary expressions over composite data types.
    /// For example, the ternary expression `cond ? (a, b) : (c, d)` is flattened into the following:
    /// ```leo
    /// let var$0 = cond ? a : c;
    /// let var$1 = cond ? b : d;
    /// (var$0, var$1)
    /// ```
    /// For circuits, the ternary expression `cond ? a : b`, where `a` and `b` are both circuits `Foo { bar: u8, baz: u8 }`, is flattened into the following:
    /// ```leo
    /// let var$0 = cond ? a.bar : b.bar;
    /// let var$1 = cond ? a.baz : b.baz;
    /// let var$2 = Foo { bar: var$0, baz: var$1 };
    /// var$2
    /// ```
    fn reconstruct_ternary(&mut self, input: TernaryExpression) -> (Expression, Self::AdditionalOutput) {
        let mut statements = Vec::new();
        match (*input.if_true, *input.if_false) {
            // Folds ternary expressions over tuples into a tuple of ternary expression.
            // Note that this branch is only invoked when folding a conditional returns.
            (Expression::Tuple(first), Expression::Tuple(second)) => {
                let tuple = Expression::Tuple(TupleExpression {
                    elements: first
                        .elements
                        .into_iter()
                        .zip_eq(second.elements.into_iter())
                        .map(|(if_true, if_false)| {
                            // Reconstruct the true case.
                            let (if_true, stmts) = self.reconstruct_expression(if_true);
                            statements.extend(stmts);

                            // Reconstruct the false case.
                            let (if_false, stmts) = self.reconstruct_expression(if_false);
                            statements.extend(stmts);

                            // Construct a new ternary expression for the tuple element.
                            let (ternary, stmts) = self.reconstruct_ternary(TernaryExpression {
                                condition: input.condition.clone(),
                                if_true: Box::new(if_true),
                                if_false: Box::new(if_false),
                                span: input.span,
                            });

                            // Accumulate any statements generated.
                            statements.extend(stmts);

                            // Create and accumulate an intermediate assignment statement for the ternary expression corresponding to the tuple element.
                            let (identifier, statement) = self.unique_simple_assign_statement(ternary);
                            statements.push(statement);

                            // Return the identifier associated with the folded tuple element.
                            Expression::Identifier(identifier)
                        })
                        .collect(),
                    span: Default::default(),
                });
                (tuple, statements)
            }
            // If both expressions are access expressions which themselves are circuits, construct ternary expression for nested circuit member.
            (
                Expression::Access(AccessExpression::Member(first)),
                Expression::Access(AccessExpression::Member(second)),
            ) => {
                // Lookup the circuit symbols associated with the expressions.
                // TODO: Remove clones
                let first_circuit_symbol =
                    self.lookup_circuit_symbol(&Expression::Access(AccessExpression::Member(first.clone())));
                let second_circuit_symbol =
                    self.lookup_circuit_symbol(&Expression::Access(AccessExpression::Member(second.clone())));

                match (first_circuit_symbol, second_circuit_symbol) {
                    (Some(first_circuit_symbol), Some(second_circuit_symbol)) => {
                        let first_member_circuit = self.symbol_table.lookup_circuit(first_circuit_symbol).unwrap();
                        let second_member_circuit = self.symbol_table.lookup_circuit(second_circuit_symbol).unwrap();
                        // Note that type checking guarantees that both expressions have the same same type. This is a sanity check.
                        assert_eq!(first_member_circuit, second_member_circuit);

                        // For each circuit member, construct a new ternary expression.
                        let members = first_member_circuit
                            .members
                            .iter()
                            .map(|CircuitMember::CircuitVariable(id, _)| {
                                // Construct a new ternary expression for the circuit member.
                                let (expression, stmts) = self.reconstruct_ternary(TernaryExpression {
                                    condition: input.condition.clone(),
                                    if_true: Box::new(Expression::Access(AccessExpression::Member(MemberAccess {
                                        inner: Box::new(Expression::Access(AccessExpression::Member(first.clone()))),
                                        name: *id,
                                        span: Default::default(),
                                    }))),
                                    if_false: Box::new(Expression::Access(AccessExpression::Member(MemberAccess {
                                        inner: Box::new(Expression::Access(AccessExpression::Member(second.clone()))),
                                        name: *id,
                                        span: Default::default(),
                                    }))),
                                    span: Default::default(),
                                });

                                // Accumulate any statements generated.
                                statements.extend(stmts);

                                // Create and accumulate an intermediate assignment statement for the ternary expression corresponding to the circuit member.
                                let (identifier, statement) = self.unique_simple_assign_statement(expression);
                                statements.push(statement);

                                CircuitVariableInitializer {
                                    identifier: *id,
                                    expression: Some(Expression::Identifier(identifier)),
                                }
                            })
                            .collect();

                        let (expr, stmts) = self.reconstruct_circuit_init(CircuitExpression {
                            name: first_member_circuit.identifier,
                            members,
                            span: Default::default(),
                        });

                        // Accumulate any statements generated.
                        statements.extend(stmts);

                        // Create a new assignment statement for the circuit expression.
                        let (identifier, statement) = self.unique_simple_assign_statement(expr);

                        // Mark the lhs of the assignment as a circuit.
                        self.circuits
                            .insert(identifier.name, first_member_circuit.identifier.name);

                        statements.push(statement);

                        (Expression::Identifier(identifier), statements)
                    }
                    _ => {
                        let if_true = Expression::Access(AccessExpression::Member(first));
                        let if_false = Expression::Access(AccessExpression::Member(second));
                        // Reconstruct the true case.
                        let (if_true, stmts) = self.reconstruct_expression(if_true);
                        statements.extend(stmts);

                        // Reconstruct the false case.
                        let (if_false, stmts) = self.reconstruct_expression(if_false);
                        statements.extend(stmts);

                        let (identifier, statement) =
                            self.unique_simple_assign_statement(Expression::Ternary(TernaryExpression {
                                condition: input.condition,
                                if_true: Box::new(if_true),
                                if_false: Box::new(if_false),
                                span: input.span,
                            }));

                        // Accumulate the new assignment statement.
                        statements.push(statement);

                        (Expression::Identifier(identifier), statements)
                    }
                }
            }
            // If both expressions are identifiers which are circuits, construct ternary expression for each of the members and a circuit expression for the result.
            (Expression::Identifier(first), Expression::Identifier(second))
                if self.circuits.contains_key(&first.name) && self.circuits.contains_key(&second.name) =>
            {
                let first_circuit = self
                    .symbol_table
                    .lookup_circuit(*self.circuits.get(&first.name).unwrap())
                    .unwrap();
                let second_circuit = self
                    .symbol_table
                    .lookup_circuit(*self.circuits.get(&second.name).unwrap())
                    .unwrap();
                // Note that type checking guarantees that both expressions have the same same type. This is a sanity check.
                assert_eq!(first_circuit, second_circuit);

                // For each circuit member, construct a new ternary expression.
                let members = first_circuit
                    .members
                    .iter()
                    .map(|CircuitMember::CircuitVariable(id, _)| {
                        // Construct a new ternary expression for the circuit member.
                        let (expression, stmts) = self.reconstruct_ternary(TernaryExpression {
                            condition: input.condition.clone(),
                            if_true: Box::new(Expression::Access(AccessExpression::Member(MemberAccess {
                                inner: Box::new(Expression::Identifier(first)),
                                name: *id,
                                span: Default::default(),
                            }))),
                            if_false: Box::new(Expression::Access(AccessExpression::Member(MemberAccess {
                                inner: Box::new(Expression::Identifier(second)),
                                name: *id,
                                span: Default::default(),
                            }))),
                            span: Default::default(),
                        });

                        // Accumulate any statements generated.
                        statements.extend(stmts);

                        // Create and accumulate an intermediate assignment statement for the ternary expression corresponding to the circuit member.
                        let (identifier, statement) = self.unique_simple_assign_statement(expression);
                        statements.push(statement);

                        CircuitVariableInitializer {
                            identifier: *id,
                            expression: Some(Expression::Identifier(identifier)),
                        }
                    })
                    .collect();

                let (expr, stmts) = self.reconstruct_circuit_init(CircuitExpression {
                    name: first_circuit.identifier,
                    members,
                    span: Default::default(),
                });

                // Accumulate any statements generated.
                statements.extend(stmts);

                // Create a new assignment statement for the circuit expression.
                let (identifier, statement) = self.unique_simple_assign_statement(expr);

                // Mark the lhs of the assignment as a circuit.
                self.circuits.insert(identifier.name, first_circuit.identifier.name);

                statements.push(statement);

                (Expression::Identifier(identifier), statements)
            }
            // Otherwise, create a new intermediate assignment for the ternary expression are return the assigned variable.
            // Note that a new assignment must be created to flattened nested ternary expressions.
            (if_true, if_false) => {
                // Reconstruct the true case.
                let (if_true, stmts) = self.reconstruct_expression(if_true);
                statements.extend(stmts);

                // Reconstruct the false case.
                let (if_false, stmts) = self.reconstruct_expression(if_false);
                statements.extend(stmts);

                let (identifier, statement) =
                    self.unique_simple_assign_statement(Expression::Ternary(TernaryExpression {
                        condition: input.condition,
                        if_true: Box::new(if_true),
                        if_false: Box::new(if_false),
                        span: input.span,
                    }));

                // Accumulate the new assignment statement.
                statements.push(statement);

                (Expression::Identifier(identifier), statements)
            }
        }
    }
}
