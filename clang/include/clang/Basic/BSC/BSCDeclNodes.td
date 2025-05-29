def Trait : DeclNode<Tag, "Traits">;
    def TraitTemplateSpecialization : DeclNode<Trait>;
def BSCMethod : DeclNode<Function>;
def ImplTrait : DeclNode<Declarator, "impltraits">;
def TraitTemplate : DeclNode<RedeclarableTemplate>;