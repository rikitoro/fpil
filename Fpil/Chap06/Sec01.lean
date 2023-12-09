-- # Structures and Inheritance

structure MythicalCreature where
  large :Bool
deriving Repr

#check MythicalCreature.mk

#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large := true
  vulnerability := "sunlight"

#check Monster.mk

#eval troll
#eval troll.toMythicalCreature

def troll' : Monster := {
  large := true,
  vulnerability := "sunlight"
}

#eval troll'
#eval troll'.toMythicalCreature

def troll'' : Monster := ⟨⟨true⟩, "sunlight"⟩

#eval troll''
#eval troll''.toMythicalCreature

#eval troll.large

#check MythicalCreature.large
-- #eval MythicalCreature.large troll

def MythicalCreature.small (c : MythicalCreature) : Bool :=
  !c.large

#eval troll.small
#check MythicalCreature.small
-- #check MythicalCreature.small troll
#check MythicalCreature.small troll.toMythicalCreature


-- # Multiple Inheritance

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

#check Helper.mk
#eval nisse

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := false
  assistance:= "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

#check MonstrousAssistant.mk
#eval domesticatedTroll
#check MonstrousAssistant.toHelper
#print MonstrousAssistant.toHelper


-- # Default Declarations

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  simp
