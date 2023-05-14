use index_vec::IndexVec;
pub use string_interner::symbol::SymbolU32 as InternedString;
use string_interner::StringInterner;
use tracing::debug;

pub use crate::typeck::hir;

/// Backing storage for the various types.
#[derive(Debug, PartialEq)]
pub struct TyCtxt<'icx> {
    pub interner: &'icx mut StringInterner,
    pub decls: IndexVec<DeclId, Decl>,
    pub types: IndexVec<TypeId, Type>,
}

impl<'icx> TyCtxt<'icx> {
    pub fn new_with_builtin_types_and_functions(interner: &'icx mut StringInterner) -> Self {
        let mut ty_ctxt = Self {
            interner,
            decls: Default::default(),
            types: Default::default(),
        };

        let unit_type_id = ty_ctxt.types.push(Type::Unit);
        let bool_type_id = ty_ctxt.types.push(Type::Bool);
        let integer_type_id = ty_ctxt.types.push(Type::Integer);
        let double_type_id = ty_ctxt.types.push(Type::Double);

        assert_eq!(*ty_ctxt.get_type(ty_ctxt.unit_type()), Type::Unit);
        assert_eq!(*ty_ctxt.get_type(ty_ctxt.bool_type()), Type::Bool);
        assert_eq!(*ty_ctxt.get_type(ty_ctxt.integer_type()), Type::Integer);
        assert_eq!(*ty_ctxt.get_type(ty_ctxt.double_type()), Type::Double);

        let dabs = Decl {
            name: ty_ctxt.interner.get_or_intern("DABS"),
            ty: ty_ctxt.alloc_type(Type::Procedure {
                params: vec![ty_ctxt.double_type()],
                ret_ty: ty_ctxt.double_type(),
            }),
        };
        ty_ctxt.alloc_decl(dabs);

        assert_eq!(*ty_ctxt.get_decl(ty_ctxt.dabs_decl()), dabs);

        ty_ctxt
    }

    pub fn unit_type(&self) -> TypeId {
        TypeId::new(0)
    }

    pub fn bool_type(&self) -> TypeId {
        TypeId::new(1)
    }

    pub fn integer_type(&self) -> TypeId {
        TypeId::new(2)
    }

    pub fn double_type(&self) -> TypeId {
        TypeId::new(3)
    }

    pub fn dabs_decl(&self) -> DeclId {
        DeclId::new(0)
    }

    pub fn alloc_decl(&mut self, decl: Decl) -> DeclId {
        self.decls.push(decl)
    }

    pub fn get_decl(&self, id: DeclId) -> &Decl {
        &self.decls[id]
    }

    pub fn alloc_type(&mut self, ty: Type) -> TypeId {
        match ty {
            Type::Procedure { .. } | Type::Array { .. } => self.types.push(ty),
            Type::Bool => self.bool_type(),
            Type::Double => self.double_type(),
            Type::Integer => self.integer_type(),
            Type::Unit => self.unit_type(),
        }
    }

    pub fn get_type(&self, id: TypeId) -> &Type {
        &self.types[id]
    }

    // Check if two types are equal. Note that this recursively checks for *structural* equivalence
    // for array types and nominal equivalence for procedures.
    pub fn type_equals(&self, a: TypeId, b: TypeId) -> bool {
        match (self.get_type(a), self.get_type(b)) {
            (
                Type::Array {
                    base_ty: a_ty,
                    dimensions: a_dim,
                },
                Type::Array {
                    base_ty: b_ty,
                    dimensions: b_dim,
                },
            ) => self.type_equals(*a_ty, *b_ty) && a_dim == b_dim,
            (Type::Procedure { .. }, Type::Procedure { .. }) => a == b,
            (Type::Unit, Type::Unit) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Double, Type::Double) => true,
            (Type::Integer, Type::Integer) => true,
            _ => false,
        }
    }
}

index_vec::define_index_type! {
    pub struct DeclId = u32;
    MAX_INDEX = i32::max_value() as usize;
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct Decl {
    pub name: InternedString,
    pub ty: TypeId,
}

index_vec::define_index_type! {
    pub struct TypeId = u32;
    MAX_INDEX = i32::max_value() as usize;
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Procedure { params: Vec<TypeId>, ret_ty: TypeId },
    Array { base_ty: TypeId, dimensions: usize },
    Integer,
    Double,
    Bool,
    Unit,
}
