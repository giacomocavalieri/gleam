use erlang_term_format::Etf;
use itertools::Itertools;

use crate::Position::FunctionStatement;

#[must_use]
/// Represents an open module that has yet to be closed.
pub struct Module {
    forms: erlang_term_format::List,
}

#[must_use]
/// Represents an open function that has yet to be closed.
/// A function definition is started with `Eaf::start_function` and _must_ be
/// closed using `Eaf::end_function`.
pub struct Function {
    clauses: erlang_term_format::List,
    statements: erlang_term_format::List,
}

#[must_use]
/// Represents an open function call that has yet to be closed.
pub struct Call {
    arguments: erlang_term_format::List,
}

/// Defines the operations to describe the content of an erlang module.
///
pub trait Eaf {
    fn start_module(&mut self, module_name: &str) -> Module;
    fn end_module(&mut self, module: Module, forms: u32);

    /// Adds to the module an export attribute for the given exported functions.
    ///
    /// For example:
    ///
    /// ```ignore
    /// eaf.export_attribute(vec![("wibble", 1), ("wobble", 2)]);
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// -export([wibble/1, wobble/2]).
    /// ```
    ///
    fn export_attribute<'a>(&mut self, exported: impl IntoIterator<Item = (&'a str, usize)>);

    /// Adds to the module a doc attribute with the given content.
    /// The doc comment will refer to the form immediately following it.
    ///
    /// For example:
    ///
    /// ```ignore
    /// eaf.doc_attribute("Some fancy docs");
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// -doc(~"Some fancy docs").
    /// ```
    ///
    fn doc_attribute(&mut self, docs: &str);

    /// This starts a module function definition.
    /// Any code generated after this is gonna be a statement of the open
    /// function until `end_function` is called.
    ///
    /// For example:
    ///
    /// ```ignore
    /// let function = eaf.start_function("first_name", 0, vec![]);
    /// eaf.string("Giacomo");
    /// eaf.end_function(function, 1);
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// first_name() -> ~"Giacomo".
    /// ```
    ///
    fn start_function<'a>(
        &mut self,
        name: &str,
        arity: usize,
        arguments_names: impl IntoIterator<Item = &'a str>,
    ) -> Function;

    /// This takes a function and the number of statements it contains and
    /// closes it.
    /// Code generated after this is not gonna be part of this function.
    ///
    /// > ⚠️ There's no check to ensure `statements` matches with the number
    /// > of statements that the function actually contains.
    /// > If you get it wrong, this will generate invalid Erlang code!
    ///
    fn end_function(&mut self, function: Function, statements: u32);

    /// This starts a remote call.
    /// Any code generated after this is gonna be an argument of the open
    /// function call `end_call` is called.
    ///
    /// For example:
    ///
    /// ```ignore
    /// let call = eaf.start_remote_call("io", "format");
    /// eaf.string("Giacomo");
    /// eaf.end_call(call, 1);
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// io:format(~"Giacomo").
    /// ```
    ///
    fn start_remote_call(&mut self, module: &str, function: &str) -> Call;

    /// This starts a function call.
    /// Any code generated after this is gonna be an argument of the open
    /// function call `end_call` is called.
    ///
    /// For example:
    ///
    /// ```ignore
    /// let call = eaf.start_call("wibble");
    /// eaf.string("Hello");
    /// eaf.string("Giacomo");
    /// eaf.end_call(call, 2);
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// wibble(~"Hello", ~"Giacomo").
    /// ```
    ///
    fn start_call(&mut self, function: &str) -> Call;

    /// This takes an open call and the number of arguments it is passed
    /// and closes it.
    /// Code generated after this is not gonna be an argument to this call.
    ///
    /// > ⚠️ There's no check to ensure `arguments` matches with the number
    /// > of arguments that the call is actually passed.
    /// > If you get it wrong, this will generate invalid Erlang code!
    ///
    fn end_call(&mut self, call: Call, arguments: u32);

    /// This creates a list.
    /// The next two generated values are going to be respectively the first
    /// item and the tail of the list.
    ///
    /// For example:
    ///
    /// ```ignore
    /// eaf.cons_list();
    /// eaf.variable("Hello");
    /// eaf.cons_list();
    /// eaf.string("Giacomo");
    /// eaf.empty_list();
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// [Hello | [ ~"Giacomo" | []]].
    /// % Which, with some syntax sugar, is how we represent a list with two
    /// % elements:
    /// % [Hello, ~"Giacomo"]
    /// ```
    ///
    fn cons_list(&mut self);

    /// This creates an empty list.
    fn empty_list(&mut self);

    /// This creates a variable with the given name.
    fn variable(&mut self, name: &str);

    /// This creates a string literal, where the string is represented as a
    /// bit array with the utf8 bytes making up the string.
    /// This is how Gleam string literals are represented in Erlang.
    ///
    /// For example:
    ///
    /// ```ignore
    /// eaf.string("ksiąskę");
    /// ```
    ///
    /// Corresponds to:
    ///
    /// ```erl
    /// ~"ksiąskę".
    /// % Which is the same as <<"ksiąskę"/utf8>>
    /// % Or the same as writing the bytes directly:
    /// % <<107, 115, 105, 196, 133, 115, 107, 196, 153>>
    /// ```
    ///
    fn string(&mut self, string: &str);
}

/// This is a data structure that can be used to produce the erlang abstract
/// format binary representation of an erlang module.
pub struct BinaryEaf {
    etf: Etf,
}

impl BinaryEaf {
    pub fn new() -> Self {
        Self { etf: Etf::new() }
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.etf.into_vec()
    }

    fn module_attribute(&mut self, module_name: &str) {
        self.etf.small_tuple(4);
        self.etf.atom("attribute");
        self.annotation();
        self.etf.atom("module");
        self.etf.atom(module_name);
    }

    /// TODO))
    fn annotation(&mut self) {
        let list = self.etf.start_list();
        self.etf.small_tuple(2);
        self.etf.atom("location");
        self.etf.usize(1);
        self.etf.end_list(list, 1);
    }

    fn variable_pattern(&mut self, argument_name: &str) {
        self.etf.small_tuple(3);
        self.etf.atom("var");
        self.annotation();
        self.etf.atom(argument_name);
    }

    /// Generates the eaf representation of an atom literal.
    fn atom_literal(&mut self, atom: &str) {
        self.etf.small_tuple(3);
        self.etf.atom("atom");
        self.annotation();
        self.etf.atom(atom);
    }

    /// Generates the eaf representation of an erlang charlist literal with the
    /// given content.
    fn charlist(&mut self, content: &str) {
        self.etf.small_tuple(3);
        self.etf.atom("string");
        self.annotation();
        let characters = self.etf.start_list();
        for char in content.bytes() {
            self.etf.usize(char as usize);
        }
        self.etf.end_list(characters, content.len() as u32);
    }
}

impl Eaf for BinaryEaf {
    fn start_module(&mut self, module_name: &str) -> Module {
        // A module is represented as just a list of forms.
        // We automatically add the module attribute at the beginning.
        let forms = self.etf.start_list();
        self.module_attribute(module_name);
        Module { forms }
    }

    fn end_module(&mut self, module: Module, forms: u32) {
        // We need to add 1 to account for the module attribute that we have
        // added ourselves when opening the module!
        self.etf.end_list(module.forms, forms + 1);
    }

    fn export_attribute<'a>(&mut self, exported: impl IntoIterator<Item = (&'a str, usize)>) {
        self.etf.small_tuple(4);
        self.etf.atom("attribute");
        self.annotation();
        self.etf.atom("export");

        let mut count = 0;
        let list = self.etf.start_list();
        for (name, arity) in exported {
            count += 1;
            self.etf.small_tuple(2);
            self.etf.atom(name);
            self.etf.usize(arity);
        }
        self.etf.end_list(list, count);
    }

    fn doc_attribute(&mut self, content: &str) {
        self.etf.small_tuple(4);
        self.etf.atom("attribute");
        self.annotation();
        self.etf.atom("doc");
        self.etf.binary(content.len() as u32, content.bytes());
    }

    fn start_function<'a>(
        &mut self,
        function_name: &str,
        arity: usize,
        arguments_names: impl IntoIterator<Item = &'a str>,
    ) -> Function {
        // A function is represented as a tuple that looks like this:
        //
        //  {function,ANNO,Name,Arity,[Rep(Fc_1), ...,Rep(Fc_k)]}
        //
        // Where `Rep(Fc_1)`, ..., `Rep(Fc_k)` are the representation of the
        // function clauses.
        // Each Gleam function is always compiled down to a function with a
        // single clause. So that list should always contain a single item.
        //
        // A clause is the represented as this:
        //
        //  {clause,ANNO,Rep(Ps),[],Rep(B)}
        //
        // - `Rep(Ps)` is the representation of the arguments of the clause.
        //   In Gleam the generated function's arguments are always gonna be
        //   simple variables (and not contain any pattern).
        // - `Rep(B)` is the representation of the statements of the clause.
        //   That is, a list with the representation of each individual
        //   statement.
        //
        // So, given how a Gleam function is compiled to erlang we can see that
        // its representation is gonna be:
        //
        //  {
        //     function, ANNO, Name, Arity, [{
        //        clause, ANNO, [{var, ANNO, arg0}, ...], [], [
        //          Rep(Statement0),
        //          Rep(Statement1),
        //          ...
        //        ]
        //     }]
        //  }

        self.etf.small_tuple(5);
        self.etf.atom("function");
        self.annotation();
        self.etf.atom(function_name);
        self.etf.usize(arity);

        // This list is gonna contain just a single clause! And we immediately
        // write the clause tuple.
        let clauses = self.etf.start_list();
        self.etf.small_tuple(5);
        self.etf.atom("clause");
        self.annotation();

        // Now we add a list with the arguments to the clause tuple.
        let arguments = self.etf.start_list();
        let mut count = 0;
        for argument_name in arguments_names {
            count += 1;
            self.variable_pattern(argument_name)
        }
        self.etf.end_list(arguments, count);

        // The spec now wants an empty list.
        self.etf.empty_list();

        // Finally we open the list that's gonna contain the function
        // statements.
        // We can't tell how long that's gonna be yet, and we'll set that length
        // only when the function body gets closed and we know how many
        // statements we've actually generated.
        let statements = self.etf.start_list();
        // Only once the caller is done adding statements we can close the
        // statements list and then the outer clauses list containing the
        // function clause.
        Function {
            clauses,
            statements,
        }
    }

    fn end_function(&mut self, function: Function, statements: u32) {
        self.etf.end_list(function.statements, statements);
        self.etf.end_list(function.clauses, 1);
    }

    fn start_remote_call(&mut self, module: &str, name: &str) -> Call {
        // A remote call is represented by the following tuple:
        //
        //   {
        //     call, ANNO, {remote, ANNO, Rep(E_m), Rep(E_0)}, [
        //       Rep(E_1),
        //       ...,
        //       Rep(E_k)
        //     ]
        //   }
        //
        self.etf.small_tuple(4);
        self.etf.atom("call");
        self.annotation();

        self.etf.small_tuple(4);
        self.etf.atom("remote");
        self.annotation();
        self.atom_literal(module);
        self.atom_literal(name);

        let arguments = self.etf.start_list();
        Call { arguments }
    }

    fn end_call(&mut self, call: Call, arguments: u32) {
        self.etf.end_list(call.arguments, arguments);
    }

    fn start_call(&mut self, function: &str) -> Call {
        // {call,ANNO,Rep(E_0),[Rep(E_1), ..., Rep(E_k)]}
        self.etf.small_tuple(4);
        self.etf.atom("call");
        self.annotation();
        self.atom_literal(function);
        let arguments = self.etf.start_list();
        Call { arguments }
    }

    fn variable(&mut self, variable: &str) {
        self.variable_pattern(variable);
    }

    fn string(&mut self, content: &str) {
        // A gleam literal string is encoded as a bitarray in erlang.
        // So a string is a bitarray with a single segment that's the bytes of
        // the utf8-encoded literal string.
        //
        // {bin,ANNO,
        // [{bin_element,ANNO,Rep(E_1),Rep(Size_1),Rep(TSL_1)}, ..., {bin_element,ANNO,Rep(E_k),Rep(Size_k),Rep(TSL_k)}]}
        self.etf.small_tuple(3);
        self.etf.atom("bin");
        self.annotation();
        let segments = self.etf.start_list();

        self.etf.small_tuple(5);
        self.etf.atom("bin_element");
        self.annotation();

        self.charlist(content);

        self.etf.atom("default");
        self.etf.atom("default");

        self.etf.end_list(segments, 1);
    }

    fn cons_list(&mut self) {
        self.etf.small_tuple(4);
        self.etf.atom("cons");
        self.annotation();
    }

    fn empty_list(&mut self) {
        self.etf.small_tuple(2);
        self.etf.atom("nil");
        self.annotation();
    }
}

/// A structure that implements the EAF trait but rather than producing the
/// erlang abstract format binary, it will produce a nice and readable erlang
/// source string that can be used for testing.
struct PrettyEaf {
    code: String,
    /// This keeps track of what we're generating
    position: Vec<Position>,
}

enum Position {
    FunctionArgument { first: bool },
    FunctionStatement { indentation: usize, first: bool },
    List { expected: ExpectedListItem },
}

enum ExpectedListItem {
    First,
    Rest,
    Done,
}

impl Eaf for PrettyEaf {
    fn start_module(&mut self, module_name: &str) -> Module {
        self.code.push_str(&format!("-module({module_name}).\n"));
        Module {
            forms: PrettyEaf::dummy_list(),
        }
    }

    fn export_attribute<'a>(&mut self, exported: impl IntoIterator<Item = (&'a str, usize)>) {
        self.code.push_str(&format!(
            "-export([{}]).\n",
            exported
                .into_iter()
                .map(|(name, arity)| { format!("{name}/{arity}") })
                .join(", ")
        ));
    }

    fn doc_attribute(&mut self, docs: &str) {
        self.code.push_str(&format!("\n-doc(~\"{docs}\")."));
    }

    fn start_function<'a>(
        &mut self,
        name: &str,
        _arity: usize,
        arguments_names: impl IntoIterator<Item = &'a str>,
    ) -> Function {
        self.code.push_str(&format!(
            "\n{name}({}) ->",
            arguments_names.into_iter().join(", ")
        ));
        self.position.push(FunctionStatement {
            first: true,
            indentation: INDENT,
        });
        Function {
            clauses: PrettyEaf::dummy_list(),
            statements: PrettyEaf::dummy_list(),
        }
    }

    fn start_remote_call(&mut self, module: &str, function: &str) -> Call {
        self.new_expression();
        self.code.push_str(&format!("{module}:{function}("));
        self.position
            .push(Position::FunctionArgument { first: true });
        Call {
            arguments: PrettyEaf::dummy_list(),
        }
    }

    fn variable(&mut self, name: &str) {
        self.new_expression();
        self.code.push_str(name);
    }

    fn string(&mut self, content: &str) {
        self.new_expression();
        self.code.push_str(&format!("~\"{content}\"",));
    }

    fn start_call(&mut self, function: &str) -> Call {
        self.new_expression();
        self.code.push_str(&format!("{function}("));
        self.position
            .push(Position::FunctionArgument { first: true });
        Call {
            arguments: PrettyEaf::dummy_list(),
        }
    }

    fn end_call(&mut self, call: Call, _arguments: u32) {
        self.close_currently_open_item();
        call.arguments.consume();
    }

    fn end_function(&mut self, function: Function, _statements: u32) {
        self.close_currently_open_item();
        function.clauses.consume();
        function.statements.consume();
    }

    fn end_module(&mut self, module: Module, _forms: u32) {
        module.forms.consume();
    }

    fn cons_list(&mut self) {
        self.new_expression();
        self.code.push('[');
        self.position.push(Position::List {
            expected: ExpectedListItem::First,
        });
    }

    fn empty_list(&mut self) {
        self.new_expression();
        self.code.push_str("[]");
    }
}

const INDENT: usize = 4;

impl PrettyEaf {
    pub fn new() -> Self {
        Self {
            code: String::new(),
            position: vec![],
        }
    }

    pub fn into_string(self) -> String {
        self.code
    }

    fn dummy_list() -> erlang_term_format::List {
        erlang_term_format::List::new(0)
    }

    fn new_expression(&mut self) {
        match self.position.last_mut() {
            Some(Position::FunctionArgument { first }) => {
                if !*first {
                    self.code.push_str(", ");
                }
                *first = false;
            }
            Some(Position::List { expected }) => match expected {
                // We're expecting the list's head. We don't have to add
                // anything!
                ExpectedListItem::First => *expected = ExpectedListItem::Rest,
                ExpectedListItem::Rest => {
                    self.code.push_str(" | ");
                    *expected = ExpectedListItem::Done
                }
                // The list is actually over, this next expression is going to
                // be outside of the list!
                ExpectedListItem::Done => {
                    self.code.push(']');
                    self.position.pop();
                    self.new_expression();
                }
            },
            Some(Position::FunctionStatement { indentation, first }) => {
                if !*first {
                    self.code.push(',');
                }
                self.code.push('\n');
                self.code.push_str(&" ".repeat(*indentation));
                *first = false;
            }
            None => (),
        }
    }

    fn close_currently_open_item(&mut self) {
        match self.position.pop() {
            None => (),
            Some(Position::List { expected }) => match expected {
                ExpectedListItem::First => panic!("popped list expecting first item"),
                ExpectedListItem::Rest => panic!("popped list expecting tail"),
                // If we're popping a position and we find a list that is done
                // we need to add the closing `]` and then keep popping.
                ExpectedListItem::Done => {
                    self.code.push(']');
                    self.close_currently_open_item();
                }
            },
            // When we're done generating statements for a function we need to
            // add one final `.` to the last statement. Then we also want to
            // add an empty line to make our code breath a bit better.
            Some(Position::FunctionStatement { .. }) => self.code.push_str(".\n"),
            // When we're done generating the arguments of a function we need
            // to add the closed parentheses for the function call!
            Some(Position::FunctionArgument { .. }) => self.code.push(')'),
        }
    }
}

pub fn wibble(eaf: &mut impl Eaf) {
    let module = eaf.start_module("wibble");

    eaf.export_attribute(vec![("name", 0)]);

    let function = eaf.start_function("name", 0, vec![]);
    eaf.string("Giacomo");
    eaf.end_function(function, 1);

    eaf.end_module(module, 2);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_wibble_test() {
        let mut eaf = PrettyEaf::new();
        wibble(&mut eaf);
        println!("{}", eaf.into_string());
    }

    #[test]
    fn bianry_wibble_test() {
        let mut eaf = BinaryEaf::new();
        wibble(&mut eaf);
        println!(
            r#"begin
  {{ok, _, Binary}} = compile:forms(binary_to_term(<<{}>>), [report]),
  ok = file:write_file("wibble.beam", Binary)
end."#,
            eaf.into_vec().iter().join(",")
        );
    }
}
