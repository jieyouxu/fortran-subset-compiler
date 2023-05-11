pub use string_interner::symbol::SymbolU32 as InternedString;

pub use crate::typeck::hir;

/// Backing storage for the various types.
#[derive(Debug, PartialEq)]
pub struct TyCtxt {
    pub decls: Vec<Decl>,
    pub types: Vec<Type>,
}

impl TyCtxt {
    pub fn new_with_builtin_types() -> Self {
        let mut ty_ctxt = Self {
            decls: vec![],
            types: vec![],
        };
        let unit_id = ty_ctxt.alloc_type(Type::Unit);
        assert_eq!(unit_id, Self::UNIT_TYPE_ID);
        let bool_id = ty_ctxt.alloc_type(Type::Bool);
        assert_eq!(bool_id, Self::BOOL_TYPE_ID);
        let int_id = ty_ctxt.alloc_type(Type::Integer);
        assert_eq!(int_id, Self::INTEGER_TYPE_ID);
        let double_id = ty_ctxt.alloc_type(Type::Double);
        assert_eq!(double_id, Self::DOUBLE_TYPE_ID);
        ty_ctxt
    }

    pub const UNIT_TYPE_ID: TypeId = TypeId(0);
    pub const BOOL_TYPE_ID: TypeId = TypeId(1);
    pub const INTEGER_TYPE_ID: TypeId = TypeId(2);
    pub const DOUBLE_TYPE_ID: TypeId = TypeId(3);

    pub fn alloc_decl(&mut self, decl: Decl) -> DeclId {
        let id = DeclId(self.decls.len());
        self.decls.push(decl);
        id
    }

    pub fn get_decl(&self, id: DeclId) -> &Decl {
        &self.decls[id.0]
    }

    pub fn alloc_type(&mut self, ty: Type) -> TypeId {
        match ty {
            Type::Procedure { .. } | Type::Array { .. } => {
                let id = TypeId(self.types.len());
                self.types.push(ty);
                id
            }
            Type::Bool => Self::BOOL_TYPE_ID,
            Type::Double => Self::DOUBLE_TYPE_ID,
            Type::Integer => Self::INTEGER_TYPE_ID,
            Type::Unit => Self::UNIT_TYPE_ID,
        }
    }

    pub fn get_type(&self, id: TypeId) -> &Type {
        &self.types[id.0]
    }
}

#[derive(Debug, PartialEq, Copy, Clone, Eq, PartialOrd, Ord)]
pub struct DeclId(usize);

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct Decl {
    pub name: InternedString,
    pub ty: TypeId,
}

#[derive(Debug, PartialEq, Copy, Clone, Eq, PartialOrd, Ord)]
pub struct TypeId(usize);

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Procedure { params: Vec<TypeId>, ret_ty: TypeId },
    Array { base_ty: TypeId, dimensions: usize },
    Integer,
    Double,
    Bool,
    Unit,
}
