use lsp_types::{CodeAction, CodeActionParams};

use crate::{ast, build, language_server, line_numbers::LineNumbers};

pub fn desugar_use<'a>(
    module: &'a build::Module,
    params: &'a CodeActionParams,
) -> Option<CodeAction> {
    let _ = DesugarUseActionBuilder::new(params, module);
    todo!()
}

struct DesugarUseActionBuilder<'a> {
    params: &'a CodeActionParams,
    line_numbers: LineNumbers,
    edits: Vec<String>,
}

impl<'a> DesugarUseActionBuilder<'a> {
    fn new(params: &'a CodeActionParams, module: &'a build::Module) -> Self {
        Self {
            line_numbers: LineNumbers::new(&module.code),
            edits: vec![],
            params,
        }
    }
}

impl<'ast> ast::visit::Visit<'ast> for DesugarUseActionBuilder<'_> {
    fn visit_typed_use(&mut self, use_: &'ast ast::TypedUse) {
        let use_range = language_server::src_span_to_lsp_range(use_.location, &self.line_numbers);
        if language_server::engine::overlaps(use_range, self.params.range) {
            todo!()
        } else {
            ast::visit::visit_typed_use(self, use_)
        }
    }
}
