use ast;
use ty;
use codemap::Spanned;
use errors::TranslationError;
use trans::{self, TranslationResult};
use trans::tables::Tables;

pub(super) fn translate_types(
    tables: &mut Tables,
    structs: Vec<ast::Struct>,
) -> TranslationResult<()> {
    // collect all names
    for s in &structs {
        if tables.types.pre_register_struct_type(s.name.clone()) {
            return error!(TranslationError::TypeAlreadyDefined(s.name.clone()), s.span);
        }
    }

    // really build structs
    for s in structs {
        let fields = s.fields
            .iter()
            .map(|&(ref name, ref aty)| {
                trans::translate_type(&mut tables.types, aty.clone(), false)
                    .map(|ty| (name.clone(), ty))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let tv = ty::TypeValue::Struct(ty::StructType {
            name: s.name.clone(),
            fields,
        });
        tables.types.register_struct_type(&s.name, tv);
    }

    Ok(())
}
