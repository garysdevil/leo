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

use crate::create_messages;
use std::fmt::{Debug, Display};

create_messages!(
    /// InputError enum that represents all the errors for the inputs part of `leo-ast` crate.
    TypeCheckerError,
    code_mask: 2000i32,
    code_prefix: "TYC",

    /// For when the parser encountered an invalid assignment target.
    @formatted
    invalid_assignment_target {
        args: (),
        msg: "invalid assignment target",
        help: None,
    }

    /// For when the user tries to assign to a const input.
    @formatted
    cannot_assign_to_const_input {
        args: (input: impl Display),
        msg: format!(
            "Cannot assign to const input `{input}`",
        ),
        help: None,
    }

    /// For when the user tries to assign to a const input.
    @formatted
    cannot_assign_to_const_var {
        args: (var: impl Display),
        msg: format!(
            "Cannot assign to const variable `{var}`",
        ),
        help: None,
    }

    /// For when the user tries to assign to a const input.
    @formatted
    type_should_be {
        args: (type_: impl Display, expected: impl Display),
        msg: format!(
            "Expected type `{expected}` but type `{type_}` was found",
        ),
        help: None,
    }

    /// For when the type checker cannot determine the type of an expression.
    @formatted
    could_not_determine_type {
        args: (expr: impl Display),
        msg: format!(
            "Could not determine the type of `{expr}`",
        ),
        help: None,
    }

    /// For when the user tries to return a unknown variable.
    @formatted
    unknown_sym {
        args: (kind: impl Display, sym: impl Display),
        msg: format!(
            "Unknown {kind} `{sym}`",
        ),
        help: None,
    }

    /// For when the user tries calls a function with the incorrect number of args.
    @formatted
    incorrect_num_args_to_call {
        args: (expected: impl Display, received: impl Display),
        msg: format!(
            "Call expected `{expected}` args, but got `{received}`",
        ),
        help: None,
    }

    /// For when one of the following types was expected.
    @formatted
    expected_one_type_of {
        args: (expected: impl Display, received: impl Display),
        msg: format!(
            "Expected one type from `{expected}`, but got `{received}`",
        ),
        help: None,
    }

    /// For when an integer is not in a valid range.
    @formatted
    invalid_int_value {
        args: (value: impl Display, type_: impl Display),
        msg: format!(
            "The value {value} is not a valid `{type_}`",
        ),
        help: None,
    }

    /// For when an invalid core instruction is used.
    @formatted
    invalid_core_instruction {
        args: (circuit: impl Display, function: impl Display),
        msg: format!(
            "The instruction {circuit}::{function} is not a valid core instruction.",
        ),
        help: None,
    }

    /// For when a circuit is created with the same name as a core type.
    @formatted
    core_type_name_conflict {
        args: (type_: impl Display),
        msg: format!(
            "The type {type_} is a reserved core type name.",
        ),
        help: None,
    }

    /// For when a function doesn't have a return statement.
    @formatted
    function_has_no_return {
        args: (func: impl Display),
        msg: format!(
            "The function {func} has no return statement.",
        ),
        help: None,
    }

    /// For when the user tries initialize a circuit with the incorrect number of args.
    @formatted
    incorrect_num_circuit_members {
        args: (expected: impl Display, received: impl Display),
        msg: format!(
            "Circuit expected `{expected}` members, but got `{received}`",
        ),
        help: None,
    }

    /// For when the user is missing a circuit member during initialization.
    @formatted
    missing_circuit_member {
        args: (circuit: impl Display, member: impl Display),
        msg: format!(
            "Circuit initialization expression for `{circuit}` is missing member `{member}`.",
        ),
        help: None,
    }

    /// An invalid access call is made e.g., `bool::MAX`
    @formatted
    invalid_core_circuit_call {
        args: (expr: impl Display),
        msg: format!(
            "{expr} is not a valid core circuit call."
        ),
        help: None,
    }

    /// Attempted to define more that one circuit member with the same name.
    @formatted
    duplicate_circuit_member {
        args: (circuit: impl Display),
        msg: format!(
            "Circuit {circuit} defined with more than one member with the same name."
        ),
        help: None,
    }

    /// Attempted to define more that one record variable with the same name.
    @formatted
    duplicate_record_variable {
        args: (record: impl Display),
        msg: format!(
            "Record {record} defined with more than one variable with the same name."
        ),
        help: None,
    }

    /// Attempted to access an invalid circuit.
    @formatted
    undefined_type {
        args: (type_: impl Display),
        msg: format!(
            "The type `{type_}` is not found in the current scope."
        ),
        help: None,
    }

    /// Attempted to access an invalid circuit variable.
    @formatted
    invalid_circuit_variable {
        args: (variable: impl Display, circuit: impl Display),
        msg: format!(
            "Circuit variable {variable} is not a member of circuit {circuit}."
        ),
        help: None,
    }

    @formatted
    required_record_variable {
        args: (name: impl Display, type_: impl Display),
        msg: format!("The `record` type requires the variable `{name}: {type_}`."),
        help: None,
    }

    @formatted
    record_var_wrong_type {
        args: (name: impl Display, type_: impl Display),
        msg: format!("The field `{name}` in a `record` must have type `{type_}`."),
        help: None,
    }

    @formatted
    compare_address {
        args: (operator: impl Display),
        msg: format!("Comparison `{operator}` is not supported for the address type."),
        help: None,
    }

    @formatted
    incorrect_tuple_length {
        args: (expected: impl Display, actual: impl Display),
        msg: format!("Expected a tuple of length `{expected}` found length `{actual}`"),
        help: None,
    }

    @formatted
    invalid_tuple {
        args: (),
        msg: "Tuples must be explicitly typed in Leo".to_string(),
        help: Some("The function definition must match the function return statement".to_string()),
    }

    @formatted
    tuple_out_of_range {
        args: (index: impl Display, length: impl Display),
        msg: format!("Tuple index `{index}` out of range for a tuple with length `{length}`"),
        help: None,
    }

    @formatted
    tuple_not_allowed {
        args: (),
        msg: format!("Tuples are only allowed as function return types."),
        help: None,
    }

    @formatted
    unreachable_code_after_return {
        args: (),
        msg: format!("Cannot reach the following statement."),
        help: Some("Remove the unreachable code.".to_string()),
    }

    @formatted
    loop_body_contains_return {
        args: (),
        msg: format!("Loop body contains a return statement or always returns."),
        help: Some("Remove the code in the loop body that always returns.".to_string()),
    }

    // TODO: Consider emitting a warning instead of an error.
    @formatted
    unknown_annotation {
        args: (annotation: impl Display),
        msg: format!("Unknown annotation: `{annotation}`."),
        help: Some("Use a valid annotation. The Leo compiler supports: `@program`".to_string()),
    }

    @formatted
    helper_function_inputs_cannot_have_modes {
        args: (),
        msg: format!("Helper functions cannot have modes associated with their inputs."),
        help: Some("Consider removing the mode or adding a `@program` annotation to the function.".to_string()),
    }

    @formatted
    circuit_or_record_cannot_contain_record {
        args: (parent: impl Display, child: impl Display),
        msg: format!("A circuit or record cannot contain another record."),
        help: Some(format!("Remove the record `{child}` from `{parent}`.")),
    }

    @formatted
    invalid_mapping_type {
        args: (component: impl Display, type_: impl Display),
        msg: format!("A mapping's {component} cannot be a {type_}"),
        help: None,
    }

    @formatted
    only_program_functions_can_have_finalize {
        args: (),
        msg: format!("Only program functions can have a `finalize` block."),
        help: Some("Remove the `finalize` block or add a `@program` annotation to the function.".to_string()),
    }

    @formatted
    finalize_input_mode_must_be_public {
        args: (),
        msg: format!("An input to a finalize block must be public."),
        help: Some("Add a `public` modifier to the input variable declaration or remove the visibility modifier entirely.".to_string()),
    }

    @formatted
    finalize_in_finalize {
        args: (),
        msg: format!("A finalize block cannot contain a finalize statement."),
        help: None,
    }

    @formatted
    increment_or_decrement_outside_finalize {
        args: (),
        msg: format!("`increment` or `decrement` statements must be inside a finalize block."),
        help: None,
    }

    @formatted
    finalize_without_finalize_block {
        args: (),
        msg: format!("Cannot use a `finalize` statement without a `finalize` block."),
        help: None,
    }

    @formatted
    loop_body_contains_finalize {
        args: (),
        msg: format!("Loop body contains a finalize statement."),
        help: Some("Remove the finalize statement.".to_string()),
    }

    @formatted
    missing_return {
        args: (),
        msg: format!("Function must return a value."),
        help: None,
    }

    @formatted
    finalize_block_must_not_be_empty {
        args: (),
        msg: format!("A finalize block cannot be empty."),
        help: None,
    }

    @formatted
    cannot_have_constant_output_mode {
        args: (),
        msg: format!("A returned value cannot be a constant."),
        help: None,
    }

    @formatted
    program_function_inputs_cannot_be_const {
        args: (),
        msg: format!("Program functions cannot have constant inputs."),
        help: None,
    }

    @formatted
    incorrect_num_args_to_finalize {
        args: (expected: impl Display, received: impl Display),
        msg: format!(
            "`finalize` expected `{expected}` args, but got `{received}`",
        ),
        help: None,
    }

    @formatted
    invalid_self_access {
        args: (),
        msg: format!("The allowed accesses to `self` are `self.caller`."),
        help: None,
    }

    @formatted
    missing_finalize {
        args: (),
        msg: format!("Function must contain a `finalize` statement on all execution paths."),
        help: None,
    }

    @formatted
    finalize_name_mismatch {
        args: (finalize_name: impl Display, function_name: impl Display),
        msg: format!("`finalize` name `{finalize_name}` does not match function name `{function_name}`"),
        help: None,
    }

    @formatted
    invalid_type {
        args: (type_: impl Display),
        msg: format!("Invalid type `{type_}`"),
        help: None,
    }

    // TODO: Eventually update to warnings.
    @formatted
    assign_unit_expression_to_variable {
        args: (),
        msg: format!("Cannot assign a unit expression to a variable."),
        help: None,
    }

    // TODO: Eventually update to warnings.
    @formatted
    singleton_tuple {
        args: (),
        msg: format!("Tuples of a single element are not allowed."),
        help: None,
    }

    // TODO: Eventually update to warnings.
    @formatted
    unit_tuple {
        args: (),
        msg: format!("Tuples of a zero elements are not allowed."),
        help: None,
    }
);
