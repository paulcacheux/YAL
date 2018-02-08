use ast;
use ty;
use codemap::Spanned;
use errors::TranslationError;
use trans::{self, TranslationResult};
use trans::context::Context;

pub(super) fn translate_types(
    context: &mut Context,
    structs: Vec<ast::Struct>,
) -> TranslationResult<()> {
    // collect all names
    for s in &structs {
        if context.types.pre_register_struct_type(s.name.clone()) {
            panic!("type already defined")
        }
    }

    // really build structs
    for s in structs {
        let fields = s.fields
            .iter()
            .map(|&(ref aty, ref name)| {
                trans::translate_type(&mut context.types, aty.clone(), false)
                    .map(|ty| (ty, name.clone()))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let tv = ty::TypeValue::Struct(ty::StructType {
            name: s.name.clone(),
            fields,
        });
        context.types.register_struct_type(&s.name, tv);
    }

    Ok(())
}
