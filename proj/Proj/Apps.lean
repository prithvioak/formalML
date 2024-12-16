-- MOCK TYPE SYSTEM FOR THE FOLLOWING SENTENCES:
-- "The cow likes the dog."
-- "The dog needs the cow."
-- "The cow needs the cow."
-- "If something needs the cow, then it likes the cow."
-- Question: "Does the cow like the cow?"

-- opaque Animal : Type
inductive Animal
  | Cow
  | Dog
  | Cat
  | Horse

opaque Likes : Animal → Animal → Prop
opaque Needs : Animal → Animal → Prop
opaque Big : Animal → Prop

-- Axioms
axiom T1 : Likes Animal.Cow Animal.Dog
axiom T2 : Needs Animal.Dog Animal.Cow
axiom T3 : Needs Animal.Cow Animal.Cow
axiom R1 : ∀ x, Needs x Animal.Cow → Likes x Animal.Cow

-- Answering question
theorem Q1 : Likes Animal.Cow Animal.Cow := by
  apply R1
  apply T3

theorem Q2 : Likes Animal.Dog Animal.Cow := by
  apply R1
  apply T2
