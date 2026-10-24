/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260Prepared
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source00 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source00 : NestedInteger.Poly 3 := leaf01260_w_inner
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment00 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment00 : NestedInteger.Poly 3 := leaf01260_w_source00.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights00 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights00_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights00_identity : leaf01260_w_weights00=IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece00 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece00 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece00_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece00_weighted : leaf01260_w_piece00=IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece00_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece00_identity : leaf01260_w_piece00=IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_segment00 :=
  IntegerWeightedOuter.checked 8 1 16 0 leaf01260_w_segment00 leaf01260_w_piece00 leaf01260_w_weights00 leaf01260_w_weights00_identity leaf01260_w_piece00_weighted
#print axioms leaf01260_w_weights00_identity
#print axioms leaf01260_w_piece00_weighted
#print axioms leaf01260_w_piece00_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source01 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source01 : NestedInteger.Poly 3 := leaf01260_w_source00.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment01 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment01 : NestedInteger.Poly 3 := leaf01260_w_source01.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights01 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights01_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights01_identity : leaf01260_w_weights01=IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece01 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece01_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece01_weighted : leaf01260_w_piece01=IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece01_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece01_identity : leaf01260_w_piece01=IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_segment01 :=
  IntegerWeightedOuter.checked 8 1 16 3 leaf01260_w_segment01 leaf01260_w_piece01 leaf01260_w_weights01 leaf01260_w_weights01_identity leaf01260_w_piece01_weighted
#print axioms leaf01260_w_weights01_identity
#print axioms leaf01260_w_piece01_weighted
#print axioms leaf01260_w_piece01_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source02 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source02 : NestedInteger.Poly 3 := leaf01260_w_source01.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment02 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment02 : NestedInteger.Poly 3 := leaf01260_w_source02.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights02 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights02 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 6 leaf01260_w_segment02)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights02_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights02_identity : leaf01260_w_weights02=IntegerWeightedOuter.weights 8 1 16 6 leaf01260_w_segment02 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece02 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece02 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights02 leaf01260_w_segment02)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece02_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece02_weighted : leaf01260_w_piece02=IntegerWeightedOuter.applyWeights leaf01260_w_weights02 leaf01260_w_segment02 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece02_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece02_identity : leaf01260_w_piece02=IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_segment02 :=
  IntegerWeightedOuter.checked 8 1 16 6 leaf01260_w_segment02 leaf01260_w_piece02 leaf01260_w_weights02 leaf01260_w_weights02_identity leaf01260_w_piece02_weighted
#print axioms leaf01260_w_weights02_identity
#print axioms leaf01260_w_piece02_weighted
#print axioms leaf01260_w_piece02_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source03 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source03 : NestedInteger.Poly 3 := leaf01260_w_source02.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment03 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment03 : NestedInteger.Poly 3 := leaf01260_w_source03.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights03 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 9 leaf01260_w_segment03)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights03_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights03_identity : leaf01260_w_weights03=IntegerWeightedOuter.weights 8 1 16 9 leaf01260_w_segment03 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece03 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece03 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights03 leaf01260_w_segment03)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece03_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece03_weighted : leaf01260_w_piece03=IntegerWeightedOuter.applyWeights leaf01260_w_weights03 leaf01260_w_segment03 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece03_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece03_identity : leaf01260_w_piece03=IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_segment03 :=
  IntegerWeightedOuter.checked 8 1 16 9 leaf01260_w_segment03 leaf01260_w_piece03 leaf01260_w_weights03 leaf01260_w_weights03_identity leaf01260_w_piece03_weighted
#print axioms leaf01260_w_weights03_identity
#print axioms leaf01260_w_piece03_weighted
#print axioms leaf01260_w_piece03_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source04 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source04 : NestedInteger.Poly 3 := leaf01260_w_source03.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment04 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment04 : NestedInteger.Poly 3 := leaf01260_w_source04.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights04 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 12 leaf01260_w_segment04)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights04_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights04_identity : leaf01260_w_weights04=IntegerWeightedOuter.weights 8 1 16 12 leaf01260_w_segment04 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece04 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece04 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights04 leaf01260_w_segment04)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece04_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece04_weighted : leaf01260_w_piece04=IntegerWeightedOuter.applyWeights leaf01260_w_weights04 leaf01260_w_segment04 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece04_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece04_identity : leaf01260_w_piece04=IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_segment04 :=
  IntegerWeightedOuter.checked 8 1 16 12 leaf01260_w_segment04 leaf01260_w_piece04 leaf01260_w_weights04 leaf01260_w_weights04_identity leaf01260_w_piece04_weighted
#print axioms leaf01260_w_weights04_identity
#print axioms leaf01260_w_piece04_weighted
#print axioms leaf01260_w_piece04_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source05 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source05 : NestedInteger.Poly 3 := leaf01260_w_source04.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment05 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment05 : NestedInteger.Poly 3 := leaf01260_w_source05.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights05 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights05 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 15 leaf01260_w_segment05)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights05_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights05_identity : leaf01260_w_weights05=IntegerWeightedOuter.weights 8 1 16 15 leaf01260_w_segment05 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece05 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece05 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights05 leaf01260_w_segment05)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece05_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece05_weighted : leaf01260_w_piece05=IntegerWeightedOuter.applyWeights leaf01260_w_weights05 leaf01260_w_segment05 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece05_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece05_identity : leaf01260_w_piece05=IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_segment05 :=
  IntegerWeightedOuter.checked 8 1 16 15 leaf01260_w_segment05 leaf01260_w_piece05 leaf01260_w_weights05 leaf01260_w_weights05_identity leaf01260_w_piece05_weighted
#print axioms leaf01260_w_weights05_identity
#print axioms leaf01260_w_piece05_weighted
#print axioms leaf01260_w_piece05_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source06 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source06 : NestedInteger.Poly 3 := leaf01260_w_source05.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment06 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment06 : NestedInteger.Poly 3 := leaf01260_w_source06.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights06 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 18 leaf01260_w_segment06)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights06_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights06_identity : leaf01260_w_weights06=IntegerWeightedOuter.weights 8 1 16 18 leaf01260_w_segment06 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece06 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece06 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights06 leaf01260_w_segment06)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece06_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece06_weighted : leaf01260_w_piece06=IntegerWeightedOuter.applyWeights leaf01260_w_weights06 leaf01260_w_segment06 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece06_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece06_identity : leaf01260_w_piece06=IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_segment06 :=
  IntegerWeightedOuter.checked 8 1 16 18 leaf01260_w_segment06 leaf01260_w_piece06 leaf01260_w_weights06 leaf01260_w_weights06_identity leaf01260_w_piece06_weighted
#print axioms leaf01260_w_weights06_identity
#print axioms leaf01260_w_piece06_weighted
#print axioms leaf01260_w_piece06_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source07 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source07 : NestedInteger.Poly 3 := leaf01260_w_source06.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment07 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment07 : NestedInteger.Poly 3 := leaf01260_w_source07.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights07 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights07_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights07_identity : leaf01260_w_weights07=IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece07 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece07 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece07_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece07_weighted : leaf01260_w_piece07=IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece07_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece07_identity : leaf01260_w_piece07=IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_segment07 :=
  IntegerWeightedOuter.checked 8 1 16 21 leaf01260_w_segment07 leaf01260_w_piece07 leaf01260_w_weights07 leaf01260_w_weights07_identity leaf01260_w_piece07_weighted
#print axioms leaf01260_w_weights07_identity
#print axioms leaf01260_w_piece07_weighted
#print axioms leaf01260_w_piece07_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source08 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source08 : NestedInteger.Poly 3 := leaf01260_w_source07.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment08 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment08 : NestedInteger.Poly 3 := leaf01260_w_source08.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights08 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights08 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 24 leaf01260_w_segment08)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights08_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights08_identity : leaf01260_w_weights08=IntegerWeightedOuter.weights 8 1 16 24 leaf01260_w_segment08 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece08 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece08 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights08 leaf01260_w_segment08)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece08_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece08_weighted : leaf01260_w_piece08=IntegerWeightedOuter.applyWeights leaf01260_w_weights08 leaf01260_w_segment08 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece08_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece08_identity : leaf01260_w_piece08=IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_segment08 :=
  IntegerWeightedOuter.checked 8 1 16 24 leaf01260_w_segment08 leaf01260_w_piece08 leaf01260_w_weights08 leaf01260_w_weights08_identity leaf01260_w_piece08_weighted
#print axioms leaf01260_w_weights08_identity
#print axioms leaf01260_w_piece08_weighted
#print axioms leaf01260_w_piece08_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source09 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source09 : NestedInteger.Poly 3 := leaf01260_w_source08.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment09 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment09 : NestedInteger.Poly 3 := leaf01260_w_source09.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights09 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights09 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights09_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights09_identity : leaf01260_w_weights09=IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece09 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece09 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece09_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece09_weighted : leaf01260_w_piece09=IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece09_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece09_identity : leaf01260_w_piece09=IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_segment09 :=
  IntegerWeightedOuter.checked 8 1 16 27 leaf01260_w_segment09 leaf01260_w_piece09 leaf01260_w_weights09 leaf01260_w_weights09_identity leaf01260_w_piece09_weighted
#print axioms leaf01260_w_weights09_identity
#print axioms leaf01260_w_piece09_weighted
#print axioms leaf01260_w_piece09_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source10 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source10 : NestedInteger.Poly 3 := leaf01260_w_source09.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment10 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment10 : NestedInteger.Poly 3 := leaf01260_w_source10.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights10 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights10 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 30 leaf01260_w_segment10)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights10_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights10_identity : leaf01260_w_weights10=IntegerWeightedOuter.weights 8 1 16 30 leaf01260_w_segment10 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece10 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece10 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights10 leaf01260_w_segment10)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece10_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece10_weighted : leaf01260_w_piece10=IntegerWeightedOuter.applyWeights leaf01260_w_weights10 leaf01260_w_segment10 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece10_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece10_identity : leaf01260_w_piece10=IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_segment10 :=
  IntegerWeightedOuter.checked 8 1 16 30 leaf01260_w_segment10 leaf01260_w_piece10 leaf01260_w_weights10 leaf01260_w_weights10_identity leaf01260_w_piece10_weighted
#print axioms leaf01260_w_weights10_identity
#print axioms leaf01260_w_piece10_weighted
#print axioms leaf01260_w_piece10_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source11 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source11 : NestedInteger.Poly 3 := leaf01260_w_source10.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment11 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment11 : NestedInteger.Poly 3 := leaf01260_w_source11.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights11 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights11 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 33 leaf01260_w_segment11)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights11_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights11_identity : leaf01260_w_weights11=IntegerWeightedOuter.weights 8 1 16 33 leaf01260_w_segment11 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece11 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece11 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights11 leaf01260_w_segment11)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece11_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece11_weighted : leaf01260_w_piece11=IntegerWeightedOuter.applyWeights leaf01260_w_weights11 leaf01260_w_segment11 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece11_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece11_identity : leaf01260_w_piece11=IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_segment11 :=
  IntegerWeightedOuter.checked 8 1 16 33 leaf01260_w_segment11 leaf01260_w_piece11 leaf01260_w_weights11 leaf01260_w_weights11_identity leaf01260_w_piece11_weighted
#print axioms leaf01260_w_weights11_identity
#print axioms leaf01260_w_piece11_weighted
#print axioms leaf01260_w_piece11_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source12 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source12 : NestedInteger.Poly 3 := leaf01260_w_source11.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment12 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment12 : NestedInteger.Poly 3 := leaf01260_w_source12.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights12 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights12 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 36 leaf01260_w_segment12)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights12_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights12_identity : leaf01260_w_weights12=IntegerWeightedOuter.weights 8 1 16 36 leaf01260_w_segment12 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece12 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece12 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights12 leaf01260_w_segment12)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece12_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece12_weighted : leaf01260_w_piece12=IntegerWeightedOuter.applyWeights leaf01260_w_weights12 leaf01260_w_segment12 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece12_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece12_identity : leaf01260_w_piece12=IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_segment12 :=
  IntegerWeightedOuter.checked 8 1 16 36 leaf01260_w_segment12 leaf01260_w_piece12 leaf01260_w_weights12 leaf01260_w_weights12_identity leaf01260_w_piece12_weighted
#print axioms leaf01260_w_weights12_identity
#print axioms leaf01260_w_piece12_weighted
#print axioms leaf01260_w_piece12_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source13 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source13 : NestedInteger.Poly 3 := leaf01260_w_source12.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment13 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment13 : NestedInteger.Poly 3 := leaf01260_w_source13.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights13 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights13 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 39 leaf01260_w_segment13)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights13_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights13_identity : leaf01260_w_weights13=IntegerWeightedOuter.weights 8 1 16 39 leaf01260_w_segment13 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece13 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece13 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights13 leaf01260_w_segment13)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece13_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece13_weighted : leaf01260_w_piece13=IntegerWeightedOuter.applyWeights leaf01260_w_weights13 leaf01260_w_segment13 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece13_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece13_identity : leaf01260_w_piece13=IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_segment13 :=
  IntegerWeightedOuter.checked 8 1 16 39 leaf01260_w_segment13 leaf01260_w_piece13 leaf01260_w_weights13 leaf01260_w_weights13_identity leaf01260_w_piece13_weighted
#print axioms leaf01260_w_weights13_identity
#print axioms leaf01260_w_piece13_weighted
#print axioms leaf01260_w_piece13_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source14 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source14 : NestedInteger.Poly 3 := leaf01260_w_source13.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment14 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment14 : NestedInteger.Poly 3 := leaf01260_w_source14.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights14 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights14 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 42 leaf01260_w_segment14)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights14_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights14_identity : leaf01260_w_weights14=IntegerWeightedOuter.weights 8 1 16 42 leaf01260_w_segment14 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece14 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece14 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights14 leaf01260_w_segment14)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece14_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece14_weighted : leaf01260_w_piece14=IntegerWeightedOuter.applyWeights leaf01260_w_weights14 leaf01260_w_segment14 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece14_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece14_identity : leaf01260_w_piece14=IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_segment14 :=
  IntegerWeightedOuter.checked 8 1 16 42 leaf01260_w_segment14 leaf01260_w_piece14 leaf01260_w_weights14 leaf01260_w_weights14_identity leaf01260_w_piece14_weighted
#print axioms leaf01260_w_weights14_identity
#print axioms leaf01260_w_piece14_weighted
#print axioms leaf01260_w_piece14_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source15 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source15 : NestedInteger.Poly 3 := leaf01260_w_source14.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment15 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment15 : NestedInteger.Poly 3 := leaf01260_w_source15.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights15 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights15 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights15_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights15_identity : leaf01260_w_weights15=IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece15 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece15 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece15_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece15_weighted : leaf01260_w_piece15=IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece15_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece15_identity : leaf01260_w_piece15=IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_segment15 :=
  IntegerWeightedOuter.checked 8 1 16 45 leaf01260_w_segment15 leaf01260_w_piece15 leaf01260_w_weights15 leaf01260_w_weights15_identity leaf01260_w_piece15_weighted
#print axioms leaf01260_w_weights15_identity
#print axioms leaf01260_w_piece15_weighted
#print axioms leaf01260_w_piece15_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source16 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source16 : NestedInteger.Poly 3 := leaf01260_w_source15.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment16 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment16 : NestedInteger.Poly 3 := leaf01260_w_source16.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights16 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights16 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 48 leaf01260_w_segment16)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights16_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights16_identity : leaf01260_w_weights16=IntegerWeightedOuter.weights 8 1 16 48 leaf01260_w_segment16 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece16 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece16 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights16 leaf01260_w_segment16)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece16_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece16_weighted : leaf01260_w_piece16=IntegerWeightedOuter.applyWeights leaf01260_w_weights16 leaf01260_w_segment16 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece16_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece16_identity : leaf01260_w_piece16=IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_segment16 :=
  IntegerWeightedOuter.checked 8 1 16 48 leaf01260_w_segment16 leaf01260_w_piece16 leaf01260_w_weights16 leaf01260_w_weights16_identity leaf01260_w_piece16_weighted
#print axioms leaf01260_w_weights16_identity
#print axioms leaf01260_w_piece16_weighted
#print axioms leaf01260_w_piece16_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source17 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source17 : NestedInteger.Poly 3 := leaf01260_w_source16.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment17 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment17 : NestedInteger.Poly 3 := leaf01260_w_source17.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights17 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights17 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 51 leaf01260_w_segment17)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights17_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights17_identity : leaf01260_w_weights17=IntegerWeightedOuter.weights 8 1 16 51 leaf01260_w_segment17 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece17 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece17 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights17 leaf01260_w_segment17)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece17_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece17_weighted : leaf01260_w_piece17=IntegerWeightedOuter.applyWeights leaf01260_w_weights17 leaf01260_w_segment17 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece17_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece17_identity : leaf01260_w_piece17=IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_segment17 :=
  IntegerWeightedOuter.checked 8 1 16 51 leaf01260_w_segment17 leaf01260_w_piece17 leaf01260_w_weights17 leaf01260_w_weights17_identity leaf01260_w_piece17_weighted
#print axioms leaf01260_w_weights17_identity
#print axioms leaf01260_w_piece17_weighted
#print axioms leaf01260_w_piece17_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source18 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source18 : NestedInteger.Poly 3 := leaf01260_w_source17.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment18 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment18 : NestedInteger.Poly 3 := leaf01260_w_source18.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights18 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights18 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 54 leaf01260_w_segment18)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights18_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights18_identity : leaf01260_w_weights18=IntegerWeightedOuter.weights 8 1 16 54 leaf01260_w_segment18 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece18 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece18 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights18 leaf01260_w_segment18)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece18_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece18_weighted : leaf01260_w_piece18=IntegerWeightedOuter.applyWeights leaf01260_w_weights18 leaf01260_w_segment18 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece18_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece18_identity : leaf01260_w_piece18=IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_segment18 :=
  IntegerWeightedOuter.checked 8 1 16 54 leaf01260_w_segment18 leaf01260_w_piece18 leaf01260_w_weights18 leaf01260_w_weights18_identity leaf01260_w_piece18_weighted
#print axioms leaf01260_w_weights18_identity
#print axioms leaf01260_w_piece18_weighted
#print axioms leaf01260_w_piece18_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source19 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source19 : NestedInteger.Poly 3 := leaf01260_w_source18.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment19 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment19 : NestedInteger.Poly 3 := leaf01260_w_source19.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights19 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights19 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 57 leaf01260_w_segment19)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights19_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights19_identity : leaf01260_w_weights19=IntegerWeightedOuter.weights 8 1 16 57 leaf01260_w_segment19 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece19 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece19 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights19 leaf01260_w_segment19)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece19_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece19_weighted : leaf01260_w_piece19=IntegerWeightedOuter.applyWeights leaf01260_w_weights19 leaf01260_w_segment19 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece19_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece19_identity : leaf01260_w_piece19=IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_segment19 :=
  IntegerWeightedOuter.checked 8 1 16 57 leaf01260_w_segment19 leaf01260_w_piece19 leaf01260_w_weights19 leaf01260_w_weights19_identity leaf01260_w_piece19_weighted
#print axioms leaf01260_w_weights19_identity
#print axioms leaf01260_w_piece19_weighted
#print axioms leaf01260_w_piece19_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source20 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source20 : NestedInteger.Poly 3 := leaf01260_w_source19.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment20 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment20 : NestedInteger.Poly 3 := leaf01260_w_source20.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights20 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights20 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 60 leaf01260_w_segment20)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights20_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights20_identity : leaf01260_w_weights20=IntegerWeightedOuter.weights 8 1 16 60 leaf01260_w_segment20 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece20 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece20 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights20 leaf01260_w_segment20)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece20_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece20_weighted : leaf01260_w_piece20=IntegerWeightedOuter.applyWeights leaf01260_w_weights20 leaf01260_w_segment20 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece20_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece20_identity : leaf01260_w_piece20=IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_segment20 :=
  IntegerWeightedOuter.checked 8 1 16 60 leaf01260_w_segment20 leaf01260_w_piece20 leaf01260_w_weights20 leaf01260_w_weights20_identity leaf01260_w_piece20_weighted
#print axioms leaf01260_w_weights20_identity
#print axioms leaf01260_w_piece20_weighted
#print axioms leaf01260_w_piece20_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source21 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source21 : NestedInteger.Poly 3 := leaf01260_w_source20.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment21 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment21 : NestedInteger.Poly 3 := leaf01260_w_source21.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights21 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights21 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 63 leaf01260_w_segment21)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights21_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights21_identity : leaf01260_w_weights21=IntegerWeightedOuter.weights 8 1 16 63 leaf01260_w_segment21 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece21 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece21 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights21 leaf01260_w_segment21)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece21_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece21_weighted : leaf01260_w_piece21=IntegerWeightedOuter.applyWeights leaf01260_w_weights21 leaf01260_w_segment21 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece21_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece21_identity : leaf01260_w_piece21=IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_segment21 :=
  IntegerWeightedOuter.checked 8 1 16 63 leaf01260_w_segment21 leaf01260_w_piece21 leaf01260_w_weights21 leaf01260_w_weights21_identity leaf01260_w_piece21_weighted
#print axioms leaf01260_w_weights21_identity
#print axioms leaf01260_w_piece21_weighted
#print axioms leaf01260_w_piece21_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source22 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source22 : NestedInteger.Poly 3 := leaf01260_w_source21.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment22 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment22 : NestedInteger.Poly 3 := leaf01260_w_source22.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights22 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights22 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights22_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights22_identity : leaf01260_w_weights22=IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece22 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece22 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece22_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece22_weighted : leaf01260_w_piece22=IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece22_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece22_identity : leaf01260_w_piece22=IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_segment22 :=
  IntegerWeightedOuter.checked 8 1 16 66 leaf01260_w_segment22 leaf01260_w_piece22 leaf01260_w_weights22 leaf01260_w_weights22_identity leaf01260_w_piece22_weighted
#print axioms leaf01260_w_weights22_identity
#print axioms leaf01260_w_piece22_weighted
#print axioms leaf01260_w_piece22_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source23 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source23 : NestedInteger.Poly 3 := leaf01260_w_source22.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment23 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment23 : NestedInteger.Poly 3 := leaf01260_w_source23.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights23 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights23 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights23_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights23_identity : leaf01260_w_weights23=IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece23 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece23 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece23_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece23_weighted : leaf01260_w_piece23=IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece23_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece23_identity : leaf01260_w_piece23=IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_segment23 :=
  IntegerWeightedOuter.checked 8 1 16 69 leaf01260_w_segment23 leaf01260_w_piece23 leaf01260_w_weights23 leaf01260_w_weights23_identity leaf01260_w_piece23_weighted
#print axioms leaf01260_w_weights23_identity
#print axioms leaf01260_w_piece23_weighted
#print axioms leaf01260_w_piece23_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source24 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source24 : NestedInteger.Poly 3 := leaf01260_w_source23.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment24 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment24 : NestedInteger.Poly 3 := leaf01260_w_source24.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights24 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights24 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 72 leaf01260_w_segment24)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights24_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights24_identity : leaf01260_w_weights24=IntegerWeightedOuter.weights 8 1 16 72 leaf01260_w_segment24 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece24 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece24 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights24 leaf01260_w_segment24)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece24_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece24_weighted : leaf01260_w_piece24=IntegerWeightedOuter.applyWeights leaf01260_w_weights24 leaf01260_w_segment24 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece24_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece24_identity : leaf01260_w_piece24=IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_segment24 :=
  IntegerWeightedOuter.checked 8 1 16 72 leaf01260_w_segment24 leaf01260_w_piece24 leaf01260_w_weights24 leaf01260_w_weights24_identity leaf01260_w_piece24_weighted
#print axioms leaf01260_w_weights24_identity
#print axioms leaf01260_w_piece24_weighted
#print axioms leaf01260_w_piece24_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source25 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source25 : NestedInteger.Poly 3 := leaf01260_w_source24.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment25 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment25 : NestedInteger.Poly 3 := leaf01260_w_source25.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights25 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights25 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 75 leaf01260_w_segment25)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights25_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights25_identity : leaf01260_w_weights25=IntegerWeightedOuter.weights 8 1 16 75 leaf01260_w_segment25 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece25 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece25 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights25 leaf01260_w_segment25)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece25_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece25_weighted : leaf01260_w_piece25=IntegerWeightedOuter.applyWeights leaf01260_w_weights25 leaf01260_w_segment25 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece25_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece25_identity : leaf01260_w_piece25=IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_segment25 :=
  IntegerWeightedOuter.checked 8 1 16 75 leaf01260_w_segment25 leaf01260_w_piece25 leaf01260_w_weights25 leaf01260_w_weights25_identity leaf01260_w_piece25_weighted
#print axioms leaf01260_w_weights25_identity
#print axioms leaf01260_w_piece25_weighted
#print axioms leaf01260_w_piece25_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source26 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source26 : NestedInteger.Poly 3 := leaf01260_w_source25.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment26 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment26 : NestedInteger.Poly 3 := leaf01260_w_source26.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights26 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights26 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights26_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights26_identity : leaf01260_w_weights26=IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece26 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece26 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece26_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece26_weighted : leaf01260_w_piece26=IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece26_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece26_identity : leaf01260_w_piece26=IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_segment26 :=
  IntegerWeightedOuter.checked 8 1 16 78 leaf01260_w_segment26 leaf01260_w_piece26 leaf01260_w_weights26 leaf01260_w_weights26_identity leaf01260_w_piece26_weighted
#print axioms leaf01260_w_weights26_identity
#print axioms leaf01260_w_piece26_weighted
#print axioms leaf01260_w_piece26_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source27 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source27 : NestedInteger.Poly 3 := leaf01260_w_source26.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment27 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment27 : NestedInteger.Poly 3 := leaf01260_w_source27.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights27 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights27 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights27_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights27_identity : leaf01260_w_weights27=IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece27 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece27 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece27_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece27_weighted : leaf01260_w_piece27=IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece27_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece27_identity : leaf01260_w_piece27=IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_segment27 :=
  IntegerWeightedOuter.checked 8 1 16 81 leaf01260_w_segment27 leaf01260_w_piece27 leaf01260_w_weights27 leaf01260_w_weights27_identity leaf01260_w_piece27_weighted
#print axioms leaf01260_w_weights27_identity
#print axioms leaf01260_w_piece27_weighted
#print axioms leaf01260_w_piece27_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source28 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source28 : NestedInteger.Poly 3 := leaf01260_w_source27.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment28 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment28 : NestedInteger.Poly 3 := leaf01260_w_source28.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights28 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights28 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights28_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights28_identity : leaf01260_w_weights28=IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece28 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece28 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece28_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece28_weighted : leaf01260_w_piece28=IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece28_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece28_identity : leaf01260_w_piece28=IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_segment28 :=
  IntegerWeightedOuter.checked 8 1 16 84 leaf01260_w_segment28 leaf01260_w_piece28 leaf01260_w_weights28 leaf01260_w_weights28_identity leaf01260_w_piece28_weighted
#print axioms leaf01260_w_weights28_identity
#print axioms leaf01260_w_piece28_weighted
#print axioms leaf01260_w_piece28_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_source29 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_source29 : NestedInteger.Poly 3 := leaf01260_w_source28.drop 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_segment29 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_segment29 : NestedInteger.Poly 3 := leaf01260_w_source29.take 3
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights29 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_weights29 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 87 leaf01260_w_segment29)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_weights29_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_weights29_identity : leaf01260_w_weights29=IntegerWeightedOuter.weights 8 1 16 87 leaf01260_w_segment29 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece29 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_piece29 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights29 leaf01260_w_segment29)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece29_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece29_weighted : leaf01260_w_piece29=IntegerWeightedOuter.applyWeights leaf01260_w_weights29 leaf01260_w_segment29 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_piece29_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_piece29_identity : leaf01260_w_piece29=IntegerOuterTerms.transform 8 1 16 87 leaf01260_w_segment29 :=
  IntegerWeightedOuter.checked 8 1 16 87 leaf01260_w_segment29 leaf01260_w_piece29 leaf01260_w_weights29 leaf01260_w_weights29_identity leaf01260_w_piece29_weighted
#print axioms leaf01260_w_weights29_identity
#print axioms leaf01260_w_piece29_weighted
#print axioms leaf01260_w_piece29_identity
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix29 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix29 : NestedInteger.Poly 3 := leaf01260_w_piece29
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix29_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 87 leaf01260_w_source29)) x := by
  have h : leaf01260_w_segment29=leaf01260_w_source29 := by decide +kernel
  rw [leaf01260_w_suffix29,leaf01260_w_piece29_identity,h]
#print axioms leaf01260_w_suffix29_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix28 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix28 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix28_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix28_join : leaf01260_w_suffix28=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix28_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_source28)) x := by
  have hlen : leaf01260_w_segment28.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source29.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_segment28)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (84+leaf01260_w_segment28.length) leaf01260_w_source29)) x := by
      rw [leaf01260_w_suffix28_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece28_identity,leaf01260_w_suffix29_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 (leaf01260_w_segment28++leaf01260_w_source29))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 84 leaf01260_w_segment28 leaf01260_w_source29 x).symm
    _ = _ := by rw [show leaf01260_w_segment28++leaf01260_w_source29=leaf01260_w_source28 from List.take_append_drop 3 leaf01260_w_source28]
#print axioms leaf01260_w_suffix28_join
#print axioms leaf01260_w_suffix28_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix27 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix27 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source28.length) leaf01260_w_piece27) leaf01260_w_suffix28)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix27_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix27_join : leaf01260_w_suffix27=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source28.length) leaf01260_w_piece27) leaf01260_w_suffix28 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix27_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_source27)) x := by
  have hlen : leaf01260_w_segment27.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source28.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_segment27)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (81+leaf01260_w_segment27.length) leaf01260_w_source28)) x := by
      rw [leaf01260_w_suffix27_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece27_identity,leaf01260_w_suffix28_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 (leaf01260_w_segment27++leaf01260_w_source28))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 81 leaf01260_w_segment27 leaf01260_w_source28 x).symm
    _ = _ := by rw [show leaf01260_w_segment27++leaf01260_w_source28=leaf01260_w_source27 from List.take_append_drop 3 leaf01260_w_source27]
#print axioms leaf01260_w_suffix27_join
#print axioms leaf01260_w_suffix27_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix26 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix26 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source27.length) leaf01260_w_piece26) leaf01260_w_suffix27)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix26_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix26_join : leaf01260_w_suffix26=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source27.length) leaf01260_w_piece26) leaf01260_w_suffix27 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix26_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_source26)) x := by
  have hlen : leaf01260_w_segment26.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source27.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_segment26)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (78+leaf01260_w_segment26.length) leaf01260_w_source27)) x := by
      rw [leaf01260_w_suffix26_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece26_identity,leaf01260_w_suffix27_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 (leaf01260_w_segment26++leaf01260_w_source27))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 78 leaf01260_w_segment26 leaf01260_w_source27 x).symm
    _ = _ := by rw [show leaf01260_w_segment26++leaf01260_w_source27=leaf01260_w_source26 from List.take_append_drop 3 leaf01260_w_source26]
#print axioms leaf01260_w_suffix26_join
#print axioms leaf01260_w_suffix26_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix25 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix25 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source26.length) leaf01260_w_piece25) leaf01260_w_suffix26)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix25_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix25_join : leaf01260_w_suffix25=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source26.length) leaf01260_w_piece25) leaf01260_w_suffix26 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix25_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_source25)) x := by
  have hlen : leaf01260_w_segment25.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source26.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_segment25)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (75+leaf01260_w_segment25.length) leaf01260_w_source26)) x := by
      rw [leaf01260_w_suffix25_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece25_identity,leaf01260_w_suffix26_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 (leaf01260_w_segment25++leaf01260_w_source26))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 75 leaf01260_w_segment25 leaf01260_w_source26 x).symm
    _ = _ := by rw [show leaf01260_w_segment25++leaf01260_w_source26=leaf01260_w_source25 from List.take_append_drop 3 leaf01260_w_source25]
#print axioms leaf01260_w_suffix25_join
#print axioms leaf01260_w_suffix25_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix24 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix24 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix24_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix24_join : leaf01260_w_suffix24=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix24_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_source24)) x := by
  have hlen : leaf01260_w_segment24.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source25.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_segment24)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (72+leaf01260_w_segment24.length) leaf01260_w_source25)) x := by
      rw [leaf01260_w_suffix24_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece24_identity,leaf01260_w_suffix25_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 (leaf01260_w_segment24++leaf01260_w_source25))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 72 leaf01260_w_segment24 leaf01260_w_source25 x).symm
    _ = _ := by rw [show leaf01260_w_segment24++leaf01260_w_source25=leaf01260_w_source24 from List.take_append_drop 3 leaf01260_w_source24]
#print axioms leaf01260_w_suffix24_join
#print axioms leaf01260_w_suffix24_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix23 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix23 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source24.length) leaf01260_w_piece23) leaf01260_w_suffix24)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix23_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix23_join : leaf01260_w_suffix23=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source24.length) leaf01260_w_piece23) leaf01260_w_suffix24 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix23_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_source23)) x := by
  have hlen : leaf01260_w_segment23.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source24.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_segment23)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (69+leaf01260_w_segment23.length) leaf01260_w_source24)) x := by
      rw [leaf01260_w_suffix23_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece23_identity,leaf01260_w_suffix24_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 (leaf01260_w_segment23++leaf01260_w_source24))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 69 leaf01260_w_segment23 leaf01260_w_source24 x).symm
    _ = _ := by rw [show leaf01260_w_segment23++leaf01260_w_source24=leaf01260_w_source23 from List.take_append_drop 3 leaf01260_w_source23]
#print axioms leaf01260_w_suffix23_join
#print axioms leaf01260_w_suffix23_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix22 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix22 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source23.length) leaf01260_w_piece22) leaf01260_w_suffix23)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix22_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix22_join : leaf01260_w_suffix22=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source23.length) leaf01260_w_piece22) leaf01260_w_suffix23 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix22_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_source22)) x := by
  have hlen : leaf01260_w_segment22.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source23.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_segment22)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (66+leaf01260_w_segment22.length) leaf01260_w_source23)) x := by
      rw [leaf01260_w_suffix22_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece22_identity,leaf01260_w_suffix23_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 (leaf01260_w_segment22++leaf01260_w_source23))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 66 leaf01260_w_segment22 leaf01260_w_source23 x).symm
    _ = _ := by rw [show leaf01260_w_segment22++leaf01260_w_source23=leaf01260_w_source22 from List.take_append_drop 3 leaf01260_w_source22]
#print axioms leaf01260_w_suffix22_join
#print axioms leaf01260_w_suffix22_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix21 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix21 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix21_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix21_join : leaf01260_w_suffix21=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix21_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_source21)) x := by
  have hlen : leaf01260_w_segment21.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source22.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_segment21)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (63+leaf01260_w_segment21.length) leaf01260_w_source22)) x := by
      rw [leaf01260_w_suffix21_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece21_identity,leaf01260_w_suffix22_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 (leaf01260_w_segment21++leaf01260_w_source22))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 63 leaf01260_w_segment21 leaf01260_w_source22 x).symm
    _ = _ := by rw [show leaf01260_w_segment21++leaf01260_w_source22=leaf01260_w_source21 from List.take_append_drop 3 leaf01260_w_source21]
#print axioms leaf01260_w_suffix21_join
#print axioms leaf01260_w_suffix21_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix20 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix20 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source21.length) leaf01260_w_piece20) leaf01260_w_suffix21)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix20_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix20_join : leaf01260_w_suffix20=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source21.length) leaf01260_w_piece20) leaf01260_w_suffix21 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix20_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_source20)) x := by
  have hlen : leaf01260_w_segment20.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source21.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_segment20)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (60+leaf01260_w_segment20.length) leaf01260_w_source21)) x := by
      rw [leaf01260_w_suffix20_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece20_identity,leaf01260_w_suffix21_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 (leaf01260_w_segment20++leaf01260_w_source21))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 60 leaf01260_w_segment20 leaf01260_w_source21 x).symm
    _ = _ := by rw [show leaf01260_w_segment20++leaf01260_w_source21=leaf01260_w_source20 from List.take_append_drop 3 leaf01260_w_source20]
#print axioms leaf01260_w_suffix20_join
#print axioms leaf01260_w_suffix20_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix19 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix19 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source20.length) leaf01260_w_piece19) leaf01260_w_suffix20)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix19_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix19_join : leaf01260_w_suffix19=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source20.length) leaf01260_w_piece19) leaf01260_w_suffix20 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix19_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix19) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_source19)) x := by
  have hlen : leaf01260_w_segment19.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source20.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_segment19)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (57+leaf01260_w_segment19.length) leaf01260_w_source20)) x := by
      rw [leaf01260_w_suffix19_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece19_identity,leaf01260_w_suffix20_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 (leaf01260_w_segment19++leaf01260_w_source20))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 57 leaf01260_w_segment19 leaf01260_w_source20 x).symm
    _ = _ := by rw [show leaf01260_w_segment19++leaf01260_w_source20=leaf01260_w_source19 from List.take_append_drop 3 leaf01260_w_source19]
#print axioms leaf01260_w_suffix19_join
#print axioms leaf01260_w_suffix19_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix18 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix18 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source19.length) leaf01260_w_piece18) leaf01260_w_suffix19)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix18_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix18_join : leaf01260_w_suffix18=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source19.length) leaf01260_w_piece18) leaf01260_w_suffix19 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix18_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix18) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_source18)) x := by
  have hlen : leaf01260_w_segment18.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source19.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_segment18)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (54+leaf01260_w_segment18.length) leaf01260_w_source19)) x := by
      rw [leaf01260_w_suffix18_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece18_identity,leaf01260_w_suffix19_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 (leaf01260_w_segment18++leaf01260_w_source19))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 54 leaf01260_w_segment18 leaf01260_w_source19 x).symm
    _ = _ := by rw [show leaf01260_w_segment18++leaf01260_w_source19=leaf01260_w_source18 from List.take_append_drop 3 leaf01260_w_source18]
#print axioms leaf01260_w_suffix18_join
#print axioms leaf01260_w_suffix18_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix17 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix17 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source18.length) leaf01260_w_piece17) leaf01260_w_suffix18)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix17_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix17_join : leaf01260_w_suffix17=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source18.length) leaf01260_w_piece17) leaf01260_w_suffix18 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix17_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix17_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix17) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_source17)) x := by
  have hlen : leaf01260_w_segment17.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source18.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_segment17)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (51+leaf01260_w_segment17.length) leaf01260_w_source18)) x := by
      rw [leaf01260_w_suffix17_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece17_identity,leaf01260_w_suffix18_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 (leaf01260_w_segment17++leaf01260_w_source18))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 51 leaf01260_w_segment17 leaf01260_w_source18 x).symm
    _ = _ := by rw [show leaf01260_w_segment17++leaf01260_w_source18=leaf01260_w_source17 from List.take_append_drop 3 leaf01260_w_source17]
#print axioms leaf01260_w_suffix17_join
#print axioms leaf01260_w_suffix17_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix16 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix16 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source17.length) leaf01260_w_piece16) leaf01260_w_suffix17)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix16_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix16_join : leaf01260_w_suffix16=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source17.length) leaf01260_w_piece16) leaf01260_w_suffix17 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix16_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix16_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix16) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_source16)) x := by
  have hlen : leaf01260_w_segment16.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source17.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_segment16)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (48+leaf01260_w_segment16.length) leaf01260_w_source17)) x := by
      rw [leaf01260_w_suffix16_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece16_identity,leaf01260_w_suffix17_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 (leaf01260_w_segment16++leaf01260_w_source17))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 48 leaf01260_w_segment16 leaf01260_w_source17 x).symm
    _ = _ := by rw [show leaf01260_w_segment16++leaf01260_w_source17=leaf01260_w_source16 from List.take_append_drop 3 leaf01260_w_source16]
#print axioms leaf01260_w_suffix16_join
#print axioms leaf01260_w_suffix16_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix15 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix15 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source16.length) leaf01260_w_piece15) leaf01260_w_suffix16)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix15_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix15_join : leaf01260_w_suffix15=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source16.length) leaf01260_w_piece15) leaf01260_w_suffix16 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix15_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix15_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix15) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_source15)) x := by
  have hlen : leaf01260_w_segment15.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source16.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_segment15)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (45+leaf01260_w_segment15.length) leaf01260_w_source16)) x := by
      rw [leaf01260_w_suffix15_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece15_identity,leaf01260_w_suffix16_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 (leaf01260_w_segment15++leaf01260_w_source16))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 45 leaf01260_w_segment15 leaf01260_w_source16 x).symm
    _ = _ := by rw [show leaf01260_w_segment15++leaf01260_w_source16=leaf01260_w_source15 from List.take_append_drop 3 leaf01260_w_source15]
#print axioms leaf01260_w_suffix15_join
#print axioms leaf01260_w_suffix15_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix14 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix14 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source15.length) leaf01260_w_piece14) leaf01260_w_suffix15)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix14_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix14_join : leaf01260_w_suffix14=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source15.length) leaf01260_w_piece14) leaf01260_w_suffix15 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix14_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix14) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_source14)) x := by
  have hlen : leaf01260_w_segment14.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source15.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_segment14)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (42+leaf01260_w_segment14.length) leaf01260_w_source15)) x := by
      rw [leaf01260_w_suffix14_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece14_identity,leaf01260_w_suffix15_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 (leaf01260_w_segment14++leaf01260_w_source15))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 42 leaf01260_w_segment14 leaf01260_w_source15 x).symm
    _ = _ := by rw [show leaf01260_w_segment14++leaf01260_w_source15=leaf01260_w_source14 from List.take_append_drop 3 leaf01260_w_source14]
#print axioms leaf01260_w_suffix14_join
#print axioms leaf01260_w_suffix14_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix13 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix13 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source14.length) leaf01260_w_piece13) leaf01260_w_suffix14)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix13_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix13_join : leaf01260_w_suffix13=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source14.length) leaf01260_w_piece13) leaf01260_w_suffix14 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix13_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix13) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_source13)) x := by
  have hlen : leaf01260_w_segment13.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source14.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_segment13)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (39+leaf01260_w_segment13.length) leaf01260_w_source14)) x := by
      rw [leaf01260_w_suffix13_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece13_identity,leaf01260_w_suffix14_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 (leaf01260_w_segment13++leaf01260_w_source14))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 39 leaf01260_w_segment13 leaf01260_w_source14 x).symm
    _ = _ := by rw [show leaf01260_w_segment13++leaf01260_w_source14=leaf01260_w_source13 from List.take_append_drop 3 leaf01260_w_source13]
#print axioms leaf01260_w_suffix13_join
#print axioms leaf01260_w_suffix13_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix12 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix12 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source13.length) leaf01260_w_piece12) leaf01260_w_suffix13)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix12_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix12_join : leaf01260_w_suffix12=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source13.length) leaf01260_w_piece12) leaf01260_w_suffix13 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix12_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix12_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix12) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_source12)) x := by
  have hlen : leaf01260_w_segment12.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source13.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_segment12)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (36+leaf01260_w_segment12.length) leaf01260_w_source13)) x := by
      rw [leaf01260_w_suffix12_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece12_identity,leaf01260_w_suffix13_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 (leaf01260_w_segment12++leaf01260_w_source13))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 36 leaf01260_w_segment12 leaf01260_w_source13 x).symm
    _ = _ := by rw [show leaf01260_w_segment12++leaf01260_w_source13=leaf01260_w_source12 from List.take_append_drop 3 leaf01260_w_source12]
#print axioms leaf01260_w_suffix12_join
#print axioms leaf01260_w_suffix12_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix11 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix11 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source12.length) leaf01260_w_piece11) leaf01260_w_suffix12)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix11_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix11_join : leaf01260_w_suffix11=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source12.length) leaf01260_w_piece11) leaf01260_w_suffix12 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix11_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix11) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_source11)) x := by
  have hlen : leaf01260_w_segment11.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source12.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_segment11)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (33+leaf01260_w_segment11.length) leaf01260_w_source12)) x := by
      rw [leaf01260_w_suffix11_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece11_identity,leaf01260_w_suffix12_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 (leaf01260_w_segment11++leaf01260_w_source12))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 33 leaf01260_w_segment11 leaf01260_w_source12 x).symm
    _ = _ := by rw [show leaf01260_w_segment11++leaf01260_w_source12=leaf01260_w_source11 from List.take_append_drop 3 leaf01260_w_source11]
#print axioms leaf01260_w_suffix11_join
#print axioms leaf01260_w_suffix11_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix10 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix10 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source11.length) leaf01260_w_piece10) leaf01260_w_suffix11)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix10_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix10_join : leaf01260_w_suffix10=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source11.length) leaf01260_w_piece10) leaf01260_w_suffix11 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix10_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix10) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_source10)) x := by
  have hlen : leaf01260_w_segment10.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source11.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_segment10)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (30+leaf01260_w_segment10.length) leaf01260_w_source11)) x := by
      rw [leaf01260_w_suffix10_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece10_identity,leaf01260_w_suffix11_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 (leaf01260_w_segment10++leaf01260_w_source11))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 30 leaf01260_w_segment10 leaf01260_w_source11 x).symm
    _ = _ := by rw [show leaf01260_w_segment10++leaf01260_w_source11=leaf01260_w_source10 from List.take_append_drop 3 leaf01260_w_source10]
#print axioms leaf01260_w_suffix10_join
#print axioms leaf01260_w_suffix10_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix09 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix09 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source10.length) leaf01260_w_piece09) leaf01260_w_suffix10)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix09_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix09_join : leaf01260_w_suffix09=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source10.length) leaf01260_w_piece09) leaf01260_w_suffix10 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix09_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_source09)) x := by
  have hlen : leaf01260_w_segment09.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source10.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_segment09)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (27+leaf01260_w_segment09.length) leaf01260_w_source10)) x := by
      rw [leaf01260_w_suffix09_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece09_identity,leaf01260_w_suffix10_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 (leaf01260_w_segment09++leaf01260_w_source10))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 27 leaf01260_w_segment09 leaf01260_w_source10 x).symm
    _ = _ := by rw [show leaf01260_w_segment09++leaf01260_w_source10=leaf01260_w_source09 from List.take_append_drop 3 leaf01260_w_source09]
#print axioms leaf01260_w_suffix09_join
#print axioms leaf01260_w_suffix09_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix08 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix08 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source09.length) leaf01260_w_piece08) leaf01260_w_suffix09)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix08_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix08_join : leaf01260_w_suffix08=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source09.length) leaf01260_w_piece08) leaf01260_w_suffix09 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix08_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_source08)) x := by
  have hlen : leaf01260_w_segment08.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source09.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_segment08)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (24+leaf01260_w_segment08.length) leaf01260_w_source09)) x := by
      rw [leaf01260_w_suffix08_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece08_identity,leaf01260_w_suffix09_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 (leaf01260_w_segment08++leaf01260_w_source09))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 24 leaf01260_w_segment08 leaf01260_w_source09 x).symm
    _ = _ := by rw [show leaf01260_w_segment08++leaf01260_w_source09=leaf01260_w_source08 from List.take_append_drop 3 leaf01260_w_source08]
#print axioms leaf01260_w_suffix08_join
#print axioms leaf01260_w_suffix08_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix07 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix07 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source08.length) leaf01260_w_piece07) leaf01260_w_suffix08)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix07_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix07_join : leaf01260_w_suffix07=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source08.length) leaf01260_w_piece07) leaf01260_w_suffix08 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix07_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_source07)) x := by
  have hlen : leaf01260_w_segment07.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source08.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_segment07)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (21+leaf01260_w_segment07.length) leaf01260_w_source08)) x := by
      rw [leaf01260_w_suffix07_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece07_identity,leaf01260_w_suffix08_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 (leaf01260_w_segment07++leaf01260_w_source08))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 21 leaf01260_w_segment07 leaf01260_w_source08 x).symm
    _ = _ := by rw [show leaf01260_w_segment07++leaf01260_w_source08=leaf01260_w_source07 from List.take_append_drop 3 leaf01260_w_source07]
#print axioms leaf01260_w_suffix07_join
#print axioms leaf01260_w_suffix07_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix06 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix06 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source07.length) leaf01260_w_piece06) leaf01260_w_suffix07)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix06_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix06_join : leaf01260_w_suffix06=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source07.length) leaf01260_w_piece06) leaf01260_w_suffix07 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix06_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_source06)) x := by
  have hlen : leaf01260_w_segment06.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (18+leaf01260_w_segment06.length) leaf01260_w_source07)) x := by
      rw [leaf01260_w_suffix06_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece06_identity,leaf01260_w_suffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 (leaf01260_w_segment06++leaf01260_w_source07))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 18 leaf01260_w_segment06 leaf01260_w_source07 x).symm
    _ = _ := by rw [show leaf01260_w_segment06++leaf01260_w_source07=leaf01260_w_source06 from List.take_append_drop 3 leaf01260_w_source06]
#print axioms leaf01260_w_suffix06_join
#print axioms leaf01260_w_suffix06_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix05 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix05 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source06.length) leaf01260_w_piece05) leaf01260_w_suffix06)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix05_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix05_join : leaf01260_w_suffix05=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source06.length) leaf01260_w_piece05) leaf01260_w_suffix06 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix05_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_source05)) x := by
  have hlen : leaf01260_w_segment05.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (15+leaf01260_w_segment05.length) leaf01260_w_source06)) x := by
      rw [leaf01260_w_suffix05_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece05_identity,leaf01260_w_suffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 (leaf01260_w_segment05++leaf01260_w_source06))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 15 leaf01260_w_segment05 leaf01260_w_source06 x).symm
    _ = _ := by rw [show leaf01260_w_segment05++leaf01260_w_source06=leaf01260_w_source05 from List.take_append_drop 3 leaf01260_w_source05]
#print axioms leaf01260_w_suffix05_join
#print axioms leaf01260_w_suffix05_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix04 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix04 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source05.length) leaf01260_w_piece04) leaf01260_w_suffix05)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix04_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix04_join : leaf01260_w_suffix04=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source05.length) leaf01260_w_piece04) leaf01260_w_suffix05 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix04_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_source04)) x := by
  have hlen : leaf01260_w_segment04.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (12+leaf01260_w_segment04.length) leaf01260_w_source05)) x := by
      rw [leaf01260_w_suffix04_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece04_identity,leaf01260_w_suffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 (leaf01260_w_segment04++leaf01260_w_source05))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 12 leaf01260_w_segment04 leaf01260_w_source05 x).symm
    _ = _ := by rw [show leaf01260_w_segment04++leaf01260_w_source05=leaf01260_w_source04 from List.take_append_drop 3 leaf01260_w_source04]
#print axioms leaf01260_w_suffix04_join
#print axioms leaf01260_w_suffix04_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix03 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix03_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix03_join : leaf01260_w_suffix03=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix03_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_source03)) x := by
  have hlen : leaf01260_w_segment03.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (9+leaf01260_w_segment03.length) leaf01260_w_source04)) x := by
      rw [leaf01260_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece03_identity,leaf01260_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 (leaf01260_w_segment03++leaf01260_w_source04))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 9 leaf01260_w_segment03 leaf01260_w_source04 x).symm
    _ = _ := by rw [show leaf01260_w_segment03++leaf01260_w_source04=leaf01260_w_source03 from List.take_append_drop 3 leaf01260_w_source03]
#print axioms leaf01260_w_suffix03_join
#print axioms leaf01260_w_suffix03_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix02 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source03.length) leaf01260_w_piece02) leaf01260_w_suffix03)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix02_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix02_join : leaf01260_w_suffix02=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source03.length) leaf01260_w_piece02) leaf01260_w_suffix03 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix02_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_source02)) x := by
  have hlen : leaf01260_w_segment02.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (6+leaf01260_w_segment02.length) leaf01260_w_source03)) x := by
      rw [leaf01260_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece02_identity,leaf01260_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 (leaf01260_w_segment02++leaf01260_w_source03))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 6 leaf01260_w_segment02 leaf01260_w_source03 x).symm
    _ = _ := by rw [show leaf01260_w_segment02++leaf01260_w_source03=leaf01260_w_source02 from List.take_append_drop 3 leaf01260_w_source02]
#print axioms leaf01260_w_suffix02_join
#print axioms leaf01260_w_suffix02_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix01 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_suffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source02.length) leaf01260_w_piece01) leaf01260_w_suffix02)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix01_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix01_join : leaf01260_w_suffix01=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source02.length) leaf01260_w_piece01) leaf01260_w_suffix02 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_suffix01_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_source01)) x := by
  have hlen : leaf01260_w_segment01.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (3+leaf01260_w_segment01.length) leaf01260_w_source02)) x := by
      rw [leaf01260_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece01_identity,leaf01260_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 (leaf01260_w_segment01++leaf01260_w_source02))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 3 leaf01260_w_segment01 leaf01260_w_source02 x).symm
    _ = _ := by rw [show leaf01260_w_segment01++leaf01260_w_source02=leaf01260_w_source01 from List.take_append_drop 3 leaf01260_w_source01]
#print axioms leaf01260_w_suffix01_join
#print axioms leaf01260_w_suffix01_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_affine MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_affine : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source01.length) leaf01260_w_piece00) leaf01260_w_suffix01)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_affine_join MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_affine_join : leaf01260_w_affine=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source01.length) leaf01260_w_piece00) leaf01260_w_suffix01 := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_affine_eval MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_source00)) x := by
  have hlen : leaf01260_w_segment00.length=3 := by decide +kernel
  calc
    _ = (16 : ℝ)^leaf01260_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 (0+leaf01260_w_segment00.length) leaf01260_w_source01)) x := by
      rw [leaf01260_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf01260_w_piece00_identity,leaf01260_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 (leaf01260_w_segment00++leaf01260_w_source01))) x :=
      (IntegerOuterPieces.eval_append 8 1 16 0 leaf01260_w_segment00 leaf01260_w_source01 x).symm
    _ = _ := by rw [show leaf01260_w_segment00++leaf01260_w_source01=leaf01260_w_source00 from List.take_append_drop 3 leaf01260_w_source00]
#print axioms leaf01260_w_affine_join
#print axioms leaf01260_w_affine_eval
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_affine_length MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_affine_length : leaf01260_w_affine.length=89 := by decide +kernel
#print axioms leaf01260_w_affine_length
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row000 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row000 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row000_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row000_weighted : leaf01260_w_row000=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row000_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row000_identity : leaf01260_w_row000=NestedInteger.coefficientFrom 88 0 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 0 0 leaf01260_w_affine leaf01260_w_row000 IntegerBernsteinWeights88.row000 (IntegerBernsteinTable.checked (n := 2) 88 0 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row000 leaf01260_w_affine_length IntegerBernsteinWeights88.row000_identity) leaf01260_w_row000_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row000_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row000_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row000=true := by decide +kernel
#print axioms leaf01260_w_row000_weighted
#print axioms leaf01260_w_row000_identity
#print axioms leaf01260_w_row000_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row001 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row001 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row001_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row001_weighted : leaf01260_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row001_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row001_identity : leaf01260_w_row001=NestedInteger.coefficientFrom 88 1 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 1 0 leaf01260_w_affine leaf01260_w_row001 IntegerBernsteinWeights88.row001 (IntegerBernsteinTable.checked (n := 2) 88 1 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row001 leaf01260_w_affine_length IntegerBernsteinWeights88.row001_identity) leaf01260_w_row001_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row001_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row001_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row001=true := by decide +kernel
#print axioms leaf01260_w_row001_weighted
#print axioms leaf01260_w_row001_identity
#print axioms leaf01260_w_row001_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row002 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row002 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row002_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row002_weighted : leaf01260_w_row002=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row002_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row002_identity : leaf01260_w_row002=NestedInteger.coefficientFrom 88 2 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 2 0 leaf01260_w_affine leaf01260_w_row002 IntegerBernsteinWeights88.row002 (IntegerBernsteinTable.checked (n := 2) 88 2 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row002 leaf01260_w_affine_length IntegerBernsteinWeights88.row002_identity) leaf01260_w_row002_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row002_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row002_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row002=true := by decide +kernel
#print axioms leaf01260_w_row002_weighted
#print axioms leaf01260_w_row002_identity
#print axioms leaf01260_w_row002_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row003 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row003 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row003_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row003_weighted : leaf01260_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row003_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row003_identity : leaf01260_w_row003=NestedInteger.coefficientFrom 88 3 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 3 0 leaf01260_w_affine leaf01260_w_row003 IntegerBernsteinWeights88.row003 (IntegerBernsteinTable.checked (n := 2) 88 3 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row003 leaf01260_w_affine_length IntegerBernsteinWeights88.row003_identity) leaf01260_w_row003_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row003_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row003_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row003=true := by decide +kernel
#print axioms leaf01260_w_row003_weighted
#print axioms leaf01260_w_row003_identity
#print axioms leaf01260_w_row003_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row004 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row004 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row004_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row004_weighted : leaf01260_w_row004=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row004_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row004_identity : leaf01260_w_row004=NestedInteger.coefficientFrom 88 4 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 4 0 leaf01260_w_affine leaf01260_w_row004 IntegerBernsteinWeights88.row004 (IntegerBernsteinTable.checked (n := 2) 88 4 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row004 leaf01260_w_affine_length IntegerBernsteinWeights88.row004_identity) leaf01260_w_row004_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row004_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row004_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row004=true := by decide +kernel
#print axioms leaf01260_w_row004_weighted
#print axioms leaf01260_w_row004_identity
#print axioms leaf01260_w_row004_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row005 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row005 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row005_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row005_weighted : leaf01260_w_row005=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row005_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row005_identity : leaf01260_w_row005=NestedInteger.coefficientFrom 88 5 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 5 0 leaf01260_w_affine leaf01260_w_row005 IntegerBernsteinWeights88.row005 (IntegerBernsteinTable.checked (n := 2) 88 5 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row005 leaf01260_w_affine_length IntegerBernsteinWeights88.row005_identity) leaf01260_w_row005_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row005_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row005_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row005=true := by decide +kernel
#print axioms leaf01260_w_row005_weighted
#print axioms leaf01260_w_row005_identity
#print axioms leaf01260_w_row005_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row006 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row006 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row006_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row006_weighted : leaf01260_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row006_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row006_identity : leaf01260_w_row006=NestedInteger.coefficientFrom 88 6 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 6 0 leaf01260_w_affine leaf01260_w_row006 IntegerBernsteinWeights88.row006 (IntegerBernsteinTable.checked (n := 2) 88 6 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row006 leaf01260_w_affine_length IntegerBernsteinWeights88.row006_identity) leaf01260_w_row006_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row006_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row006_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row006=true := by decide +kernel
#print axioms leaf01260_w_row006_weighted
#print axioms leaf01260_w_row006_identity
#print axioms leaf01260_w_row006_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row007 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row007 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row007_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row007_weighted : leaf01260_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row007_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row007_identity : leaf01260_w_row007=NestedInteger.coefficientFrom 88 7 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 7 0 leaf01260_w_affine leaf01260_w_row007 IntegerBernsteinWeights88.row007 (IntegerBernsteinTable.checked (n := 2) 88 7 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row007 leaf01260_w_affine_length IntegerBernsteinWeights88.row007_identity) leaf01260_w_row007_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row007_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row007_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row007=true := by decide +kernel
#print axioms leaf01260_w_row007_weighted
#print axioms leaf01260_w_row007_identity
#print axioms leaf01260_w_row007_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row008 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row008 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row008_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row008_weighted : leaf01260_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row008_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row008_identity : leaf01260_w_row008=NestedInteger.coefficientFrom 88 8 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 8 0 leaf01260_w_affine leaf01260_w_row008 IntegerBernsteinWeights88.row008 (IntegerBernsteinTable.checked (n := 2) 88 8 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row008 leaf01260_w_affine_length IntegerBernsteinWeights88.row008_identity) leaf01260_w_row008_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row008_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row008_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row008=true := by decide +kernel
#print axioms leaf01260_w_row008_weighted
#print axioms leaf01260_w_row008_identity
#print axioms leaf01260_w_row008_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row009 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row009 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row009_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row009_weighted : leaf01260_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row009_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row009_identity : leaf01260_w_row009=NestedInteger.coefficientFrom 88 9 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 9 0 leaf01260_w_affine leaf01260_w_row009 IntegerBernsteinWeights88.row009 (IntegerBernsteinTable.checked (n := 2) 88 9 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row009 leaf01260_w_affine_length IntegerBernsteinWeights88.row009_identity) leaf01260_w_row009_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row009_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row009_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row009=true := by decide +kernel
#print axioms leaf01260_w_row009_weighted
#print axioms leaf01260_w_row009_identity
#print axioms leaf01260_w_row009_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row010 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row010 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row010_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row010_weighted : leaf01260_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row010_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row010_identity : leaf01260_w_row010=NestedInteger.coefficientFrom 88 10 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 10 0 leaf01260_w_affine leaf01260_w_row010 IntegerBernsteinWeights88.row010 (IntegerBernsteinTable.checked (n := 2) 88 10 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row010 leaf01260_w_affine_length IntegerBernsteinWeights88.row010_identity) leaf01260_w_row010_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row010_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row010_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row010=true := by decide +kernel
#print axioms leaf01260_w_row010_weighted
#print axioms leaf01260_w_row010_identity
#print axioms leaf01260_w_row010_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row011 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row011 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row011_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row011_weighted : leaf01260_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row011_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row011_identity : leaf01260_w_row011=NestedInteger.coefficientFrom 88 11 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 11 0 leaf01260_w_affine leaf01260_w_row011 IntegerBernsteinWeights88.row011 (IntegerBernsteinTable.checked (n := 2) 88 11 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row011 leaf01260_w_affine_length IntegerBernsteinWeights88.row011_identity) leaf01260_w_row011_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row011_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row011_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row011=true := by decide +kernel
#print axioms leaf01260_w_row011_weighted
#print axioms leaf01260_w_row011_identity
#print axioms leaf01260_w_row011_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row012 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row012 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row012_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row012_weighted : leaf01260_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row012_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row012_identity : leaf01260_w_row012=NestedInteger.coefficientFrom 88 12 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 12 0 leaf01260_w_affine leaf01260_w_row012 IntegerBernsteinWeights88.row012 (IntegerBernsteinTable.checked (n := 2) 88 12 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row012 leaf01260_w_affine_length IntegerBernsteinWeights88.row012_identity) leaf01260_w_row012_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row012_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row012_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row012=true := by decide +kernel
#print axioms leaf01260_w_row012_weighted
#print axioms leaf01260_w_row012_identity
#print axioms leaf01260_w_row012_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row013 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row013 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row013_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row013_weighted : leaf01260_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row013_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row013_identity : leaf01260_w_row013=NestedInteger.coefficientFrom 88 13 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 13 0 leaf01260_w_affine leaf01260_w_row013 IntegerBernsteinWeights88.row013 (IntegerBernsteinTable.checked (n := 2) 88 13 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row013 leaf01260_w_affine_length IntegerBernsteinWeights88.row013_identity) leaf01260_w_row013_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row013_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row013_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row013=true := by decide +kernel
#print axioms leaf01260_w_row013_weighted
#print axioms leaf01260_w_row013_identity
#print axioms leaf01260_w_row013_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row014 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row014 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row014_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row014_weighted : leaf01260_w_row014=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row014_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row014_identity : leaf01260_w_row014=NestedInteger.coefficientFrom 88 14 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 14 0 leaf01260_w_affine leaf01260_w_row014 IntegerBernsteinWeights88.row014 (IntegerBernsteinTable.checked (n := 2) 88 14 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row014 leaf01260_w_affine_length IntegerBernsteinWeights88.row014_identity) leaf01260_w_row014_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row014_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row014_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row014=true := by decide +kernel
#print axioms leaf01260_w_row014_weighted
#print axioms leaf01260_w_row014_identity
#print axioms leaf01260_w_row014_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row015 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row015 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row015_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row015_weighted : leaf01260_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row015_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row015_identity : leaf01260_w_row015=NestedInteger.coefficientFrom 88 15 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 15 0 leaf01260_w_affine leaf01260_w_row015 IntegerBernsteinWeights88.row015 (IntegerBernsteinTable.checked (n := 2) 88 15 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row015 leaf01260_w_affine_length IntegerBernsteinWeights88.row015_identity) leaf01260_w_row015_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row015_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row015_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row015=true := by decide +kernel
#print axioms leaf01260_w_row015_weighted
#print axioms leaf01260_w_row015_identity
#print axioms leaf01260_w_row015_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row016 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row016 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row016_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row016_weighted : leaf01260_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row016_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row016_identity : leaf01260_w_row016=NestedInteger.coefficientFrom 88 16 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 16 0 leaf01260_w_affine leaf01260_w_row016 IntegerBernsteinWeights88.row016 (IntegerBernsteinTable.checked (n := 2) 88 16 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row016 leaf01260_w_affine_length IntegerBernsteinWeights88.row016_identity) leaf01260_w_row016_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row016_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row016_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row016=true := by decide +kernel
#print axioms leaf01260_w_row016_weighted
#print axioms leaf01260_w_row016_identity
#print axioms leaf01260_w_row016_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row017 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row017 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row017_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row017_weighted : leaf01260_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row017_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row017_identity : leaf01260_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf01260_w_affine leaf01260_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row017 leaf01260_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf01260_w_row017_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row017_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row017=true := by decide +kernel
#print axioms leaf01260_w_row017_weighted
#print axioms leaf01260_w_row017_identity
#print axioms leaf01260_w_row017_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row018 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row018 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row018_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row018_weighted : leaf01260_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row018_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row018_identity : leaf01260_w_row018=NestedInteger.coefficientFrom 88 18 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 18 0 leaf01260_w_affine leaf01260_w_row018 IntegerBernsteinWeights88.row018 (IntegerBernsteinTable.checked (n := 2) 88 18 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row018 leaf01260_w_affine_length IntegerBernsteinWeights88.row018_identity) leaf01260_w_row018_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row018_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row018_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row018=true := by decide +kernel
#print axioms leaf01260_w_row018_weighted
#print axioms leaf01260_w_row018_identity
#print axioms leaf01260_w_row018_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row019 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row019 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row019_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row019_weighted : leaf01260_w_row019=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row019_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row019_identity : leaf01260_w_row019=NestedInteger.coefficientFrom 88 19 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 19 0 leaf01260_w_affine leaf01260_w_row019 IntegerBernsteinWeights88.row019 (IntegerBernsteinTable.checked (n := 2) 88 19 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row019 leaf01260_w_affine_length IntegerBernsteinWeights88.row019_identity) leaf01260_w_row019_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row019_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row019_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row019=true := by decide +kernel
#print axioms leaf01260_w_row019_weighted
#print axioms leaf01260_w_row019_identity
#print axioms leaf01260_w_row019_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row020 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row020 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row020_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row020_weighted : leaf01260_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row020_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row020_identity : leaf01260_w_row020=NestedInteger.coefficientFrom 88 20 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 20 0 leaf01260_w_affine leaf01260_w_row020 IntegerBernsteinWeights88.row020 (IntegerBernsteinTable.checked (n := 2) 88 20 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row020 leaf01260_w_affine_length IntegerBernsteinWeights88.row020_identity) leaf01260_w_row020_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row020_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row020_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row020=true := by decide +kernel
#print axioms leaf01260_w_row020_weighted
#print axioms leaf01260_w_row020_identity
#print axioms leaf01260_w_row020_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row021 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row021 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row021_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row021_weighted : leaf01260_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row021_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row021_identity : leaf01260_w_row021=NestedInteger.coefficientFrom 88 21 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 21 0 leaf01260_w_affine leaf01260_w_row021 IntegerBernsteinWeights88.row021 (IntegerBernsteinTable.checked (n := 2) 88 21 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row021 leaf01260_w_affine_length IntegerBernsteinWeights88.row021_identity) leaf01260_w_row021_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row021_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row021_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row021=true := by decide +kernel
#print axioms leaf01260_w_row021_weighted
#print axioms leaf01260_w_row021_identity
#print axioms leaf01260_w_row021_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row022 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row022 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row022_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row022_weighted : leaf01260_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row022_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row022_identity : leaf01260_w_row022=NestedInteger.coefficientFrom 88 22 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 22 0 leaf01260_w_affine leaf01260_w_row022 IntegerBernsteinWeights88.row022 (IntegerBernsteinTable.checked (n := 2) 88 22 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row022 leaf01260_w_affine_length IntegerBernsteinWeights88.row022_identity) leaf01260_w_row022_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row022_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row022_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row022=true := by decide +kernel
#print axioms leaf01260_w_row022_weighted
#print axioms leaf01260_w_row022_identity
#print axioms leaf01260_w_row022_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row023 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row023 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row023_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row023_weighted : leaf01260_w_row023=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row023_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row023_identity : leaf01260_w_row023=NestedInteger.coefficientFrom 88 23 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 23 0 leaf01260_w_affine leaf01260_w_row023 IntegerBernsteinWeights88.row023 (IntegerBernsteinTable.checked (n := 2) 88 23 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row023 leaf01260_w_affine_length IntegerBernsteinWeights88.row023_identity) leaf01260_w_row023_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row023_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row023_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row023=true := by decide +kernel
#print axioms leaf01260_w_row023_weighted
#print axioms leaf01260_w_row023_identity
#print axioms leaf01260_w_row023_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row024 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row024 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row024_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row024_weighted : leaf01260_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row024_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row024_identity : leaf01260_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01260_w_affine leaf01260_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row024 leaf01260_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01260_w_row024_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row024_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row024=true := by decide +kernel
#print axioms leaf01260_w_row024_weighted
#print axioms leaf01260_w_row024_identity
#print axioms leaf01260_w_row024_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row025 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row025 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row025_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row025_weighted : leaf01260_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row025_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row025_identity : leaf01260_w_row025=NestedInteger.coefficientFrom 88 25 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 25 0 leaf01260_w_affine leaf01260_w_row025 IntegerBernsteinWeights88.row025 (IntegerBernsteinTable.checked (n := 2) 88 25 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row025 leaf01260_w_affine_length IntegerBernsteinWeights88.row025_identity) leaf01260_w_row025_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row025_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row025_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row025=true := by decide +kernel
#print axioms leaf01260_w_row025_weighted
#print axioms leaf01260_w_row025_identity
#print axioms leaf01260_w_row025_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row026 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row026 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row026_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row026_weighted : leaf01260_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row026_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row026_identity : leaf01260_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf01260_w_affine leaf01260_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row026 leaf01260_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf01260_w_row026_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row026_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row026=true := by decide +kernel
#print axioms leaf01260_w_row026_weighted
#print axioms leaf01260_w_row026_identity
#print axioms leaf01260_w_row026_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row027 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row027 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row027_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row027_weighted : leaf01260_w_row027=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row027_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row027_identity : leaf01260_w_row027=NestedInteger.coefficientFrom 88 27 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 27 0 leaf01260_w_affine leaf01260_w_row027 IntegerBernsteinWeights88.row027 (IntegerBernsteinTable.checked (n := 2) 88 27 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row027 leaf01260_w_affine_length IntegerBernsteinWeights88.row027_identity) leaf01260_w_row027_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row027_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row027_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row027=true := by decide +kernel
#print axioms leaf01260_w_row027_weighted
#print axioms leaf01260_w_row027_identity
#print axioms leaf01260_w_row027_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row028 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row028 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row028_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row028_weighted : leaf01260_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row028_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row028_identity : leaf01260_w_row028=NestedInteger.coefficientFrom 88 28 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 28 0 leaf01260_w_affine leaf01260_w_row028 IntegerBernsteinWeights88.row028 (IntegerBernsteinTable.checked (n := 2) 88 28 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row028 leaf01260_w_affine_length IntegerBernsteinWeights88.row028_identity) leaf01260_w_row028_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row028_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row028_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row028=true := by decide +kernel
#print axioms leaf01260_w_row028_weighted
#print axioms leaf01260_w_row028_identity
#print axioms leaf01260_w_row028_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row029 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row029 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row029_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row029_weighted : leaf01260_w_row029=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row029_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row029_identity : leaf01260_w_row029=NestedInteger.coefficientFrom 88 29 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 29 0 leaf01260_w_affine leaf01260_w_row029 IntegerBernsteinWeights88.row029 (IntegerBernsteinTable.checked (n := 2) 88 29 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row029 leaf01260_w_affine_length IntegerBernsteinWeights88.row029_identity) leaf01260_w_row029_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row029_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row029_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row029=true := by decide +kernel
#print axioms leaf01260_w_row029_weighted
#print axioms leaf01260_w_row029_identity
#print axioms leaf01260_w_row029_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row030 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row030 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row030_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row030_weighted : leaf01260_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row030_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row030_identity : leaf01260_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf01260_w_affine leaf01260_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row030 leaf01260_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf01260_w_row030_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row030_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row030=true := by decide +kernel
#print axioms leaf01260_w_row030_weighted
#print axioms leaf01260_w_row030_identity
#print axioms leaf01260_w_row030_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row031 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row031 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row031_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row031_weighted : leaf01260_w_row031=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row031_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row031_identity : leaf01260_w_row031=NestedInteger.coefficientFrom 88 31 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 31 0 leaf01260_w_affine leaf01260_w_row031 IntegerBernsteinWeights88.row031 (IntegerBernsteinTable.checked (n := 2) 88 31 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row031 leaf01260_w_affine_length IntegerBernsteinWeights88.row031_identity) leaf01260_w_row031_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row031_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row031_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row031=true := by decide +kernel
#print axioms leaf01260_w_row031_weighted
#print axioms leaf01260_w_row031_identity
#print axioms leaf01260_w_row031_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row032 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row032 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row032_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row032_weighted : leaf01260_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row032_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row032_identity : leaf01260_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01260_w_affine leaf01260_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row032 leaf01260_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01260_w_row032_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row032_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row032=true := by decide +kernel
#print axioms leaf01260_w_row032_weighted
#print axioms leaf01260_w_row032_identity
#print axioms leaf01260_w_row032_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row033 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row033 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row033_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row033_weighted : leaf01260_w_row033=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row033_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row033_identity : leaf01260_w_row033=NestedInteger.coefficientFrom 88 33 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 33 0 leaf01260_w_affine leaf01260_w_row033 IntegerBernsteinWeights88.row033 (IntegerBernsteinTable.checked (n := 2) 88 33 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row033 leaf01260_w_affine_length IntegerBernsteinWeights88.row033_identity) leaf01260_w_row033_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row033_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row033_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row033=true := by decide +kernel
#print axioms leaf01260_w_row033_weighted
#print axioms leaf01260_w_row033_identity
#print axioms leaf01260_w_row033_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row034 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row034 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row034_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row034_weighted : leaf01260_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row034_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row034_identity : leaf01260_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf01260_w_affine leaf01260_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row034 leaf01260_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf01260_w_row034_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row034_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row034=true := by decide +kernel
#print axioms leaf01260_w_row034_weighted
#print axioms leaf01260_w_row034_identity
#print axioms leaf01260_w_row034_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row035 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row035 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row035_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row035_weighted : leaf01260_w_row035=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row035_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row035_identity : leaf01260_w_row035=NestedInteger.coefficientFrom 88 35 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 35 0 leaf01260_w_affine leaf01260_w_row035 IntegerBernsteinWeights88.row035 (IntegerBernsteinTable.checked (n := 2) 88 35 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row035 leaf01260_w_affine_length IntegerBernsteinWeights88.row035_identity) leaf01260_w_row035_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row035_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row035_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row035=true := by decide +kernel
#print axioms leaf01260_w_row035_weighted
#print axioms leaf01260_w_row035_identity
#print axioms leaf01260_w_row035_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row036 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row036 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row036_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row036_weighted : leaf01260_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row036_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row036_identity : leaf01260_w_row036=NestedInteger.coefficientFrom 88 36 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 36 0 leaf01260_w_affine leaf01260_w_row036 IntegerBernsteinWeights88.row036 (IntegerBernsteinTable.checked (n := 2) 88 36 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row036 leaf01260_w_affine_length IntegerBernsteinWeights88.row036_identity) leaf01260_w_row036_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row036_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row036_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row036=true := by decide +kernel
#print axioms leaf01260_w_row036_weighted
#print axioms leaf01260_w_row036_identity
#print axioms leaf01260_w_row036_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row037 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row037 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row037_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row037_weighted : leaf01260_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row037_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row037_identity : leaf01260_w_row037=NestedInteger.coefficientFrom 88 37 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 37 0 leaf01260_w_affine leaf01260_w_row037 IntegerBernsteinWeights88.row037 (IntegerBernsteinTable.checked (n := 2) 88 37 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row037 leaf01260_w_affine_length IntegerBernsteinWeights88.row037_identity) leaf01260_w_row037_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row037_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row037_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row037=true := by decide +kernel
#print axioms leaf01260_w_row037_weighted
#print axioms leaf01260_w_row037_identity
#print axioms leaf01260_w_row037_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row038 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row038 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row038_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row038_weighted : leaf01260_w_row038=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row038_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row038_identity : leaf01260_w_row038=NestedInteger.coefficientFrom 88 38 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 38 0 leaf01260_w_affine leaf01260_w_row038 IntegerBernsteinWeights88.row038 (IntegerBernsteinTable.checked (n := 2) 88 38 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row038 leaf01260_w_affine_length IntegerBernsteinWeights88.row038_identity) leaf01260_w_row038_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row038_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row038_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row038=true := by decide +kernel
#print axioms leaf01260_w_row038_weighted
#print axioms leaf01260_w_row038_identity
#print axioms leaf01260_w_row038_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row039 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row039 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row039_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row039_weighted : leaf01260_w_row039=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row039_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row039_identity : leaf01260_w_row039=NestedInteger.coefficientFrom 88 39 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 39 0 leaf01260_w_affine leaf01260_w_row039 IntegerBernsteinWeights88.row039 (IntegerBernsteinTable.checked (n := 2) 88 39 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row039 leaf01260_w_affine_length IntegerBernsteinWeights88.row039_identity) leaf01260_w_row039_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row039_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row039_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row039=true := by decide +kernel
#print axioms leaf01260_w_row039_weighted
#print axioms leaf01260_w_row039_identity
#print axioms leaf01260_w_row039_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row040 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row040 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row040_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row040_weighted : leaf01260_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row040_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row040_identity : leaf01260_w_row040=NestedInteger.coefficientFrom 88 40 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 40 0 leaf01260_w_affine leaf01260_w_row040 IntegerBernsteinWeights88.row040 (IntegerBernsteinTable.checked (n := 2) 88 40 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row040 leaf01260_w_affine_length IntegerBernsteinWeights88.row040_identity) leaf01260_w_row040_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row040_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row040_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row040=true := by decide +kernel
#print axioms leaf01260_w_row040_weighted
#print axioms leaf01260_w_row040_identity
#print axioms leaf01260_w_row040_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row041 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row041 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row041_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row041_weighted : leaf01260_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row041_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row041_identity : leaf01260_w_row041=NestedInteger.coefficientFrom 88 41 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 41 0 leaf01260_w_affine leaf01260_w_row041 IntegerBernsteinWeights88.row041 (IntegerBernsteinTable.checked (n := 2) 88 41 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row041 leaf01260_w_affine_length IntegerBernsteinWeights88.row041_identity) leaf01260_w_row041_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row041_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row041_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row041=true := by decide +kernel
#print axioms leaf01260_w_row041_weighted
#print axioms leaf01260_w_row041_identity
#print axioms leaf01260_w_row041_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row042 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row042 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row042_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row042_weighted : leaf01260_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row042_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row042_identity : leaf01260_w_row042=NestedInteger.coefficientFrom 88 42 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 42 0 leaf01260_w_affine leaf01260_w_row042 IntegerBernsteinWeights88.row042 (IntegerBernsteinTable.checked (n := 2) 88 42 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row042 leaf01260_w_affine_length IntegerBernsteinWeights88.row042_identity) leaf01260_w_row042_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row042_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row042_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row042=true := by decide +kernel
#print axioms leaf01260_w_row042_weighted
#print axioms leaf01260_w_row042_identity
#print axioms leaf01260_w_row042_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row043 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row043 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row043_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row043_weighted : leaf01260_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row043_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row043_identity : leaf01260_w_row043=NestedInteger.coefficientFrom 88 43 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 43 0 leaf01260_w_affine leaf01260_w_row043 IntegerBernsteinWeights88.row043 (IntegerBernsteinTable.checked (n := 2) 88 43 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row043 leaf01260_w_affine_length IntegerBernsteinWeights88.row043_identity) leaf01260_w_row043_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row043_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row043_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row043=true := by decide +kernel
#print axioms leaf01260_w_row043_weighted
#print axioms leaf01260_w_row043_identity
#print axioms leaf01260_w_row043_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row044 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row044 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row044_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row044_weighted : leaf01260_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row044_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row044_identity : leaf01260_w_row044=NestedInteger.coefficientFrom 88 44 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 44 0 leaf01260_w_affine leaf01260_w_row044 IntegerBernsteinWeights88.row044 (IntegerBernsteinTable.checked (n := 2) 88 44 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row044 leaf01260_w_affine_length IntegerBernsteinWeights88.row044_identity) leaf01260_w_row044_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row044_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row044_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row044=true := by decide +kernel
#print axioms leaf01260_w_row044_weighted
#print axioms leaf01260_w_row044_identity
#print axioms leaf01260_w_row044_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row045 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row045 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row045_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row045_weighted : leaf01260_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row045_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row045_identity : leaf01260_w_row045=NestedInteger.coefficientFrom 88 45 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 45 0 leaf01260_w_affine leaf01260_w_row045 IntegerBernsteinWeights88.row045 (IntegerBernsteinTable.checked (n := 2) 88 45 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row045 leaf01260_w_affine_length IntegerBernsteinWeights88.row045_identity) leaf01260_w_row045_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row045_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row045_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row045=true := by decide +kernel
#print axioms leaf01260_w_row045_weighted
#print axioms leaf01260_w_row045_identity
#print axioms leaf01260_w_row045_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row046 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row046 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row046_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row046_weighted : leaf01260_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row046_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row046_identity : leaf01260_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf01260_w_affine leaf01260_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row046 leaf01260_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf01260_w_row046_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row046_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row046=true := by decide +kernel
#print axioms leaf01260_w_row046_weighted
#print axioms leaf01260_w_row046_identity
#print axioms leaf01260_w_row046_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row047 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row047 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row047_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row047_weighted : leaf01260_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row047_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row047_identity : leaf01260_w_row047=NestedInteger.coefficientFrom 88 47 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 47 0 leaf01260_w_affine leaf01260_w_row047 IntegerBernsteinWeights88.row047 (IntegerBernsteinTable.checked (n := 2) 88 47 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row047 leaf01260_w_affine_length IntegerBernsteinWeights88.row047_identity) leaf01260_w_row047_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row047_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row047_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row047=true := by decide +kernel
#print axioms leaf01260_w_row047_weighted
#print axioms leaf01260_w_row047_identity
#print axioms leaf01260_w_row047_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row048 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row048 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row048_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row048_weighted : leaf01260_w_row048=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row048_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row048_identity : leaf01260_w_row048=NestedInteger.coefficientFrom 88 48 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 48 0 leaf01260_w_affine leaf01260_w_row048 IntegerBernsteinWeights88.row048 (IntegerBernsteinTable.checked (n := 2) 88 48 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row048 leaf01260_w_affine_length IntegerBernsteinWeights88.row048_identity) leaf01260_w_row048_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row048_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row048_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row048=true := by decide +kernel
#print axioms leaf01260_w_row048_weighted
#print axioms leaf01260_w_row048_identity
#print axioms leaf01260_w_row048_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row049 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row049 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row049_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row049_weighted : leaf01260_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row049_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row049_identity : leaf01260_w_row049=NestedInteger.coefficientFrom 88 49 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 49 0 leaf01260_w_affine leaf01260_w_row049 IntegerBernsteinWeights88.row049 (IntegerBernsteinTable.checked (n := 2) 88 49 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row049 leaf01260_w_affine_length IntegerBernsteinWeights88.row049_identity) leaf01260_w_row049_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row049_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row049_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row049=true := by decide +kernel
#print axioms leaf01260_w_row049_weighted
#print axioms leaf01260_w_row049_identity
#print axioms leaf01260_w_row049_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row050 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row050 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row050_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row050_weighted : leaf01260_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row050_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row050_identity : leaf01260_w_row050=NestedInteger.coefficientFrom 88 50 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 50 0 leaf01260_w_affine leaf01260_w_row050 IntegerBernsteinWeights88.row050 (IntegerBernsteinTable.checked (n := 2) 88 50 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row050 leaf01260_w_affine_length IntegerBernsteinWeights88.row050_identity) leaf01260_w_row050_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row050_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row050_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row050=true := by decide +kernel
#print axioms leaf01260_w_row050_weighted
#print axioms leaf01260_w_row050_identity
#print axioms leaf01260_w_row050_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row051 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row051 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row051_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row051_weighted : leaf01260_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row051_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row051_identity : leaf01260_w_row051=NestedInteger.coefficientFrom 88 51 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 51 0 leaf01260_w_affine leaf01260_w_row051 IntegerBernsteinWeights88.row051 (IntegerBernsteinTable.checked (n := 2) 88 51 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row051 leaf01260_w_affine_length IntegerBernsteinWeights88.row051_identity) leaf01260_w_row051_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row051_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row051_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row051=true := by decide +kernel
#print axioms leaf01260_w_row051_weighted
#print axioms leaf01260_w_row051_identity
#print axioms leaf01260_w_row051_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row052 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row052 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row052_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row052_weighted : leaf01260_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row052_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row052_identity : leaf01260_w_row052=NestedInteger.coefficientFrom 88 52 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 52 0 leaf01260_w_affine leaf01260_w_row052 IntegerBernsteinWeights88.row052 (IntegerBernsteinTable.checked (n := 2) 88 52 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row052 leaf01260_w_affine_length IntegerBernsteinWeights88.row052_identity) leaf01260_w_row052_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row052_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row052_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row052=true := by decide +kernel
#print axioms leaf01260_w_row052_weighted
#print axioms leaf01260_w_row052_identity
#print axioms leaf01260_w_row052_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row053 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row053 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row053_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row053_weighted : leaf01260_w_row053=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row053_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row053_identity : leaf01260_w_row053=NestedInteger.coefficientFrom 88 53 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 53 0 leaf01260_w_affine leaf01260_w_row053 IntegerBernsteinWeights88.row053 (IntegerBernsteinTable.checked (n := 2) 88 53 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row053 leaf01260_w_affine_length IntegerBernsteinWeights88.row053_identity) leaf01260_w_row053_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row053_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row053_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row053=true := by decide +kernel
#print axioms leaf01260_w_row053_weighted
#print axioms leaf01260_w_row053_identity
#print axioms leaf01260_w_row053_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row054 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row054 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row054_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row054_weighted : leaf01260_w_row054=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row054_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row054_identity : leaf01260_w_row054=NestedInteger.coefficientFrom 88 54 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 54 0 leaf01260_w_affine leaf01260_w_row054 IntegerBernsteinWeights88.row054 (IntegerBernsteinTable.checked (n := 2) 88 54 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row054 leaf01260_w_affine_length IntegerBernsteinWeights88.row054_identity) leaf01260_w_row054_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row054_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row054_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row054=true := by decide +kernel
#print axioms leaf01260_w_row054_weighted
#print axioms leaf01260_w_row054_identity
#print axioms leaf01260_w_row054_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row055 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row055 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row055_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row055_weighted : leaf01260_w_row055=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row055_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row055_identity : leaf01260_w_row055=NestedInteger.coefficientFrom 88 55 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 55 0 leaf01260_w_affine leaf01260_w_row055 IntegerBernsteinWeights88.row055 (IntegerBernsteinTable.checked (n := 2) 88 55 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row055 leaf01260_w_affine_length IntegerBernsteinWeights88.row055_identity) leaf01260_w_row055_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row055_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row055_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row055=true := by decide +kernel
#print axioms leaf01260_w_row055_weighted
#print axioms leaf01260_w_row055_identity
#print axioms leaf01260_w_row055_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row056 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row056 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row056_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row056_weighted : leaf01260_w_row056=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row056_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row056_identity : leaf01260_w_row056=NestedInteger.coefficientFrom 88 56 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 56 0 leaf01260_w_affine leaf01260_w_row056 IntegerBernsteinWeights88.row056 (IntegerBernsteinTable.checked (n := 2) 88 56 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row056 leaf01260_w_affine_length IntegerBernsteinWeights88.row056_identity) leaf01260_w_row056_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row056_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row056_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row056=true := by decide +kernel
#print axioms leaf01260_w_row056_weighted
#print axioms leaf01260_w_row056_identity
#print axioms leaf01260_w_row056_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row057 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row057 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row057_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row057_weighted : leaf01260_w_row057=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row057_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row057_identity : leaf01260_w_row057=NestedInteger.coefficientFrom 88 57 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 57 0 leaf01260_w_affine leaf01260_w_row057 IntegerBernsteinWeights88.row057 (IntegerBernsteinTable.checked (n := 2) 88 57 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row057 leaf01260_w_affine_length IntegerBernsteinWeights88.row057_identity) leaf01260_w_row057_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row057_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row057_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row057=true := by decide +kernel
#print axioms leaf01260_w_row057_weighted
#print axioms leaf01260_w_row057_identity
#print axioms leaf01260_w_row057_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row058 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row058 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row058_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row058_weighted : leaf01260_w_row058=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row058_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row058_identity : leaf01260_w_row058=NestedInteger.coefficientFrom 88 58 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 58 0 leaf01260_w_affine leaf01260_w_row058 IntegerBernsteinWeights88.row058 (IntegerBernsteinTable.checked (n := 2) 88 58 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row058 leaf01260_w_affine_length IntegerBernsteinWeights88.row058_identity) leaf01260_w_row058_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row058_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row058_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row058=true := by decide +kernel
#print axioms leaf01260_w_row058_weighted
#print axioms leaf01260_w_row058_identity
#print axioms leaf01260_w_row058_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row059 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row059 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row059_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row059_weighted : leaf01260_w_row059=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row059_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row059_identity : leaf01260_w_row059=NestedInteger.coefficientFrom 88 59 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 59 0 leaf01260_w_affine leaf01260_w_row059 IntegerBernsteinWeights88.row059 (IntegerBernsteinTable.checked (n := 2) 88 59 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row059 leaf01260_w_affine_length IntegerBernsteinWeights88.row059_identity) leaf01260_w_row059_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row059_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row059_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row059=true := by decide +kernel
#print axioms leaf01260_w_row059_weighted
#print axioms leaf01260_w_row059_identity
#print axioms leaf01260_w_row059_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row060 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row060 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row060_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row060_weighted : leaf01260_w_row060=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row060_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row060_identity : leaf01260_w_row060=NestedInteger.coefficientFrom 88 60 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 60 0 leaf01260_w_affine leaf01260_w_row060 IntegerBernsteinWeights88.row060 (IntegerBernsteinTable.checked (n := 2) 88 60 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row060 leaf01260_w_affine_length IntegerBernsteinWeights88.row060_identity) leaf01260_w_row060_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row060_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row060_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row060=true := by decide +kernel
#print axioms leaf01260_w_row060_weighted
#print axioms leaf01260_w_row060_identity
#print axioms leaf01260_w_row060_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row061 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row061 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row061_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row061_weighted : leaf01260_w_row061=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row061_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row061_identity : leaf01260_w_row061=NestedInteger.coefficientFrom 88 61 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 61 0 leaf01260_w_affine leaf01260_w_row061 IntegerBernsteinWeights88.row061 (IntegerBernsteinTable.checked (n := 2) 88 61 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row061 leaf01260_w_affine_length IntegerBernsteinWeights88.row061_identity) leaf01260_w_row061_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row061_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row061_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row061=true := by decide +kernel
#print axioms leaf01260_w_row061_weighted
#print axioms leaf01260_w_row061_identity
#print axioms leaf01260_w_row061_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row062 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row062 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row062_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row062_weighted : leaf01260_w_row062=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row062_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row062_identity : leaf01260_w_row062=NestedInteger.coefficientFrom 88 62 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 62 0 leaf01260_w_affine leaf01260_w_row062 IntegerBernsteinWeights88.row062 (IntegerBernsteinTable.checked (n := 2) 88 62 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row062 leaf01260_w_affine_length IntegerBernsteinWeights88.row062_identity) leaf01260_w_row062_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row062_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row062_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row062=true := by decide +kernel
#print axioms leaf01260_w_row062_weighted
#print axioms leaf01260_w_row062_identity
#print axioms leaf01260_w_row062_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row063 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row063 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row063_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row063_weighted : leaf01260_w_row063=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row063_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row063_identity : leaf01260_w_row063=NestedInteger.coefficientFrom 88 63 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 63 0 leaf01260_w_affine leaf01260_w_row063 IntegerBernsteinWeights88.row063 (IntegerBernsteinTable.checked (n := 2) 88 63 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row063 leaf01260_w_affine_length IntegerBernsteinWeights88.row063_identity) leaf01260_w_row063_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row063_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row063_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row063=true := by decide +kernel
#print axioms leaf01260_w_row063_weighted
#print axioms leaf01260_w_row063_identity
#print axioms leaf01260_w_row063_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row064 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row064 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row064_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row064_weighted : leaf01260_w_row064=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row064_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row064_identity : leaf01260_w_row064=NestedInteger.coefficientFrom 88 64 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 64 0 leaf01260_w_affine leaf01260_w_row064 IntegerBernsteinWeights88.row064 (IntegerBernsteinTable.checked (n := 2) 88 64 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row064 leaf01260_w_affine_length IntegerBernsteinWeights88.row064_identity) leaf01260_w_row064_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row064_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row064_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row064=true := by decide +kernel
#print axioms leaf01260_w_row064_weighted
#print axioms leaf01260_w_row064_identity
#print axioms leaf01260_w_row064_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row065 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row065 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row065_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row065_weighted : leaf01260_w_row065=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row065_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row065_identity : leaf01260_w_row065=NestedInteger.coefficientFrom 88 65 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 65 0 leaf01260_w_affine leaf01260_w_row065 IntegerBernsteinWeights88.row065 (IntegerBernsteinTable.checked (n := 2) 88 65 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row065 leaf01260_w_affine_length IntegerBernsteinWeights88.row065_identity) leaf01260_w_row065_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row065_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row065_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row065=true := by decide +kernel
#print axioms leaf01260_w_row065_weighted
#print axioms leaf01260_w_row065_identity
#print axioms leaf01260_w_row065_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row066 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row066 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row066_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row066_weighted : leaf01260_w_row066=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row066_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row066_identity : leaf01260_w_row066=NestedInteger.coefficientFrom 88 66 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 66 0 leaf01260_w_affine leaf01260_w_row066 IntegerBernsteinWeights88.row066 (IntegerBernsteinTable.checked (n := 2) 88 66 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row066 leaf01260_w_affine_length IntegerBernsteinWeights88.row066_identity) leaf01260_w_row066_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row066_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row066_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row066=true := by decide +kernel
#print axioms leaf01260_w_row066_weighted
#print axioms leaf01260_w_row066_identity
#print axioms leaf01260_w_row066_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row067 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row067 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row067_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row067_weighted : leaf01260_w_row067=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row067_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row067_identity : leaf01260_w_row067=NestedInteger.coefficientFrom 88 67 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 67 0 leaf01260_w_affine leaf01260_w_row067 IntegerBernsteinWeights88.row067 (IntegerBernsteinTable.checked (n := 2) 88 67 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row067 leaf01260_w_affine_length IntegerBernsteinWeights88.row067_identity) leaf01260_w_row067_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row067_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row067_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row067=true := by decide +kernel
#print axioms leaf01260_w_row067_weighted
#print axioms leaf01260_w_row067_identity
#print axioms leaf01260_w_row067_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row068 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row068 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row068_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row068_weighted : leaf01260_w_row068=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row068_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row068_identity : leaf01260_w_row068=NestedInteger.coefficientFrom 88 68 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 68 0 leaf01260_w_affine leaf01260_w_row068 IntegerBernsteinWeights88.row068 (IntegerBernsteinTable.checked (n := 2) 88 68 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row068 leaf01260_w_affine_length IntegerBernsteinWeights88.row068_identity) leaf01260_w_row068_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row068_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row068_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row068=true := by decide +kernel
#print axioms leaf01260_w_row068_weighted
#print axioms leaf01260_w_row068_identity
#print axioms leaf01260_w_row068_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row069 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row069 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row069_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row069_weighted : leaf01260_w_row069=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row069_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row069_identity : leaf01260_w_row069=NestedInteger.coefficientFrom 88 69 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 69 0 leaf01260_w_affine leaf01260_w_row069 IntegerBernsteinWeights88.row069 (IntegerBernsteinTable.checked (n := 2) 88 69 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row069 leaf01260_w_affine_length IntegerBernsteinWeights88.row069_identity) leaf01260_w_row069_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row069_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row069_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row069=true := by decide +kernel
#print axioms leaf01260_w_row069_weighted
#print axioms leaf01260_w_row069_identity
#print axioms leaf01260_w_row069_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row070 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row070 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row070_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row070_weighted : leaf01260_w_row070=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row070_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row070_identity : leaf01260_w_row070=NestedInteger.coefficientFrom 88 70 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 70 0 leaf01260_w_affine leaf01260_w_row070 IntegerBernsteinWeights88.row070 (IntegerBernsteinTable.checked (n := 2) 88 70 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row070 leaf01260_w_affine_length IntegerBernsteinWeights88.row070_identity) leaf01260_w_row070_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row070_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row070_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row070=true := by decide +kernel
#print axioms leaf01260_w_row070_weighted
#print axioms leaf01260_w_row070_identity
#print axioms leaf01260_w_row070_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row071 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row071 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row071_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row071_weighted : leaf01260_w_row071=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row071_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row071_identity : leaf01260_w_row071=NestedInteger.coefficientFrom 88 71 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 71 0 leaf01260_w_affine leaf01260_w_row071 IntegerBernsteinWeights88.row071 (IntegerBernsteinTable.checked (n := 2) 88 71 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row071 leaf01260_w_affine_length IntegerBernsteinWeights88.row071_identity) leaf01260_w_row071_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row071_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row071_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row071=true := by decide +kernel
#print axioms leaf01260_w_row071_weighted
#print axioms leaf01260_w_row071_identity
#print axioms leaf01260_w_row071_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row072 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row072 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row072_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row072_weighted : leaf01260_w_row072=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row072_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row072_identity : leaf01260_w_row072=NestedInteger.coefficientFrom 88 72 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 72 0 leaf01260_w_affine leaf01260_w_row072 IntegerBernsteinWeights88.row072 (IntegerBernsteinTable.checked (n := 2) 88 72 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row072 leaf01260_w_affine_length IntegerBernsteinWeights88.row072_identity) leaf01260_w_row072_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row072_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row072_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row072=true := by decide +kernel
#print axioms leaf01260_w_row072_weighted
#print axioms leaf01260_w_row072_identity
#print axioms leaf01260_w_row072_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row073 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row073 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row073_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row073_weighted : leaf01260_w_row073=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row073_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row073_identity : leaf01260_w_row073=NestedInteger.coefficientFrom 88 73 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 73 0 leaf01260_w_affine leaf01260_w_row073 IntegerBernsteinWeights88.row073 (IntegerBernsteinTable.checked (n := 2) 88 73 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row073 leaf01260_w_affine_length IntegerBernsteinWeights88.row073_identity) leaf01260_w_row073_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row073_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row073_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row073=true := by decide +kernel
#print axioms leaf01260_w_row073_weighted
#print axioms leaf01260_w_row073_identity
#print axioms leaf01260_w_row073_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row074 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row074 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row074_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row074_weighted : leaf01260_w_row074=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row074_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row074_identity : leaf01260_w_row074=NestedInteger.coefficientFrom 88 74 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 74 0 leaf01260_w_affine leaf01260_w_row074 IntegerBernsteinWeights88.row074 (IntegerBernsteinTable.checked (n := 2) 88 74 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row074 leaf01260_w_affine_length IntegerBernsteinWeights88.row074_identity) leaf01260_w_row074_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row074_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row074_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row074=true := by decide +kernel
#print axioms leaf01260_w_row074_weighted
#print axioms leaf01260_w_row074_identity
#print axioms leaf01260_w_row074_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row075 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row075 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row075_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row075_weighted : leaf01260_w_row075=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row075_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row075_identity : leaf01260_w_row075=NestedInteger.coefficientFrom 88 75 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 75 0 leaf01260_w_affine leaf01260_w_row075 IntegerBernsteinWeights88.row075 (IntegerBernsteinTable.checked (n := 2) 88 75 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row075 leaf01260_w_affine_length IntegerBernsteinWeights88.row075_identity) leaf01260_w_row075_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row075_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row075_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row075=true := by decide +kernel
#print axioms leaf01260_w_row075_weighted
#print axioms leaf01260_w_row075_identity
#print axioms leaf01260_w_row075_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row076 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row076 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row076_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row076_weighted : leaf01260_w_row076=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row076_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row076_identity : leaf01260_w_row076=NestedInteger.coefficientFrom 88 76 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 76 0 leaf01260_w_affine leaf01260_w_row076 IntegerBernsteinWeights88.row076 (IntegerBernsteinTable.checked (n := 2) 88 76 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row076 leaf01260_w_affine_length IntegerBernsteinWeights88.row076_identity) leaf01260_w_row076_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row076_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row076_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row076=true := by decide +kernel
#print axioms leaf01260_w_row076_weighted
#print axioms leaf01260_w_row076_identity
#print axioms leaf01260_w_row076_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row077 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row077 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row077_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row077_weighted : leaf01260_w_row077=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row077_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row077_identity : leaf01260_w_row077=NestedInteger.coefficientFrom 88 77 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 77 0 leaf01260_w_affine leaf01260_w_row077 IntegerBernsteinWeights88.row077 (IntegerBernsteinTable.checked (n := 2) 88 77 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row077 leaf01260_w_affine_length IntegerBernsteinWeights88.row077_identity) leaf01260_w_row077_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row077_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row077_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row077=true := by decide +kernel
#print axioms leaf01260_w_row077_weighted
#print axioms leaf01260_w_row077_identity
#print axioms leaf01260_w_row077_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row078 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row078 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row078_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row078_weighted : leaf01260_w_row078=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row078_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row078_identity : leaf01260_w_row078=NestedInteger.coefficientFrom 88 78 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 78 0 leaf01260_w_affine leaf01260_w_row078 IntegerBernsteinWeights88.row078 (IntegerBernsteinTable.checked (n := 2) 88 78 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row078 leaf01260_w_affine_length IntegerBernsteinWeights88.row078_identity) leaf01260_w_row078_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row078_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row078_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row078=true := by decide +kernel
#print axioms leaf01260_w_row078_weighted
#print axioms leaf01260_w_row078_identity
#print axioms leaf01260_w_row078_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row079 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row079 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row079_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row079_weighted : leaf01260_w_row079=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row079_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row079_identity : leaf01260_w_row079=NestedInteger.coefficientFrom 88 79 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 79 0 leaf01260_w_affine leaf01260_w_row079 IntegerBernsteinWeights88.row079 (IntegerBernsteinTable.checked (n := 2) 88 79 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row079 leaf01260_w_affine_length IntegerBernsteinWeights88.row079_identity) leaf01260_w_row079_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row079_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row079_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row079=true := by decide +kernel
#print axioms leaf01260_w_row079_weighted
#print axioms leaf01260_w_row079_identity
#print axioms leaf01260_w_row079_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row080 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row080 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row080_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row080_weighted : leaf01260_w_row080=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row080_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row080_identity : leaf01260_w_row080=NestedInteger.coefficientFrom 88 80 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 80 0 leaf01260_w_affine leaf01260_w_row080 IntegerBernsteinWeights88.row080 (IntegerBernsteinTable.checked (n := 2) 88 80 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row080 leaf01260_w_affine_length IntegerBernsteinWeights88.row080_identity) leaf01260_w_row080_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row080_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row080_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row080=true := by decide +kernel
#print axioms leaf01260_w_row080_weighted
#print axioms leaf01260_w_row080_identity
#print axioms leaf01260_w_row080_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row081 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row081 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row081_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row081_weighted : leaf01260_w_row081=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row081_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row081_identity : leaf01260_w_row081=NestedInteger.coefficientFrom 88 81 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 81 0 leaf01260_w_affine leaf01260_w_row081 IntegerBernsteinWeights88.row081 (IntegerBernsteinTable.checked (n := 2) 88 81 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row081 leaf01260_w_affine_length IntegerBernsteinWeights88.row081_identity) leaf01260_w_row081_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row081_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row081_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row081=true := by decide +kernel
#print axioms leaf01260_w_row081_weighted
#print axioms leaf01260_w_row081_identity
#print axioms leaf01260_w_row081_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row082 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row082 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row082_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row082_weighted : leaf01260_w_row082=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row082_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row082_identity : leaf01260_w_row082=NestedInteger.coefficientFrom 88 82 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 82 0 leaf01260_w_affine leaf01260_w_row082 IntegerBernsteinWeights88.row082 (IntegerBernsteinTable.checked (n := 2) 88 82 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row082 leaf01260_w_affine_length IntegerBernsteinWeights88.row082_identity) leaf01260_w_row082_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row082_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row082_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row082=true := by decide +kernel
#print axioms leaf01260_w_row082_weighted
#print axioms leaf01260_w_row082_identity
#print axioms leaf01260_w_row082_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row083 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row083 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row083_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row083_weighted : leaf01260_w_row083=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row083_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row083_identity : leaf01260_w_row083=NestedInteger.coefficientFrom 88 83 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 83 0 leaf01260_w_affine leaf01260_w_row083 IntegerBernsteinWeights88.row083 (IntegerBernsteinTable.checked (n := 2) 88 83 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row083 leaf01260_w_affine_length IntegerBernsteinWeights88.row083_identity) leaf01260_w_row083_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row083_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row083_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row083=true := by decide +kernel
#print axioms leaf01260_w_row083_weighted
#print axioms leaf01260_w_row083_identity
#print axioms leaf01260_w_row083_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row084 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row084 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row084_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row084_weighted : leaf01260_w_row084=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row084_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row084_identity : leaf01260_w_row084=NestedInteger.coefficientFrom 88 84 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 84 0 leaf01260_w_affine leaf01260_w_row084 IntegerBernsteinWeights88.row084 (IntegerBernsteinTable.checked (n := 2) 88 84 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row084 leaf01260_w_affine_length IntegerBernsteinWeights88.row084_identity) leaf01260_w_row084_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row084_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row084_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row084=true := by decide +kernel
#print axioms leaf01260_w_row084_weighted
#print axioms leaf01260_w_row084_identity
#print axioms leaf01260_w_row084_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row085 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row085 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row085_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row085_weighted : leaf01260_w_row085=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row085_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row085_identity : leaf01260_w_row085=NestedInteger.coefficientFrom 88 85 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 85 0 leaf01260_w_affine leaf01260_w_row085 IntegerBernsteinWeights88.row085 (IntegerBernsteinTable.checked (n := 2) 88 85 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row085 leaf01260_w_affine_length IntegerBernsteinWeights88.row085_identity) leaf01260_w_row085_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row085_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row085_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row085=true := by decide +kernel
#print axioms leaf01260_w_row085_weighted
#print axioms leaf01260_w_row085_identity
#print axioms leaf01260_w_row085_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row086 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row086 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row086_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row086_weighted : leaf01260_w_row086=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row086_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row086_identity : leaf01260_w_row086=NestedInteger.coefficientFrom 88 86 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 86 0 leaf01260_w_affine leaf01260_w_row086 IntegerBernsteinWeights88.row086 (IntegerBernsteinTable.checked (n := 2) 88 86 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row086 leaf01260_w_affine_length IntegerBernsteinWeights88.row086_identity) leaf01260_w_row086_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row086_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row086_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row086=true := by decide +kernel
#print axioms leaf01260_w_row086_weighted
#print axioms leaf01260_w_row086_identity
#print axioms leaf01260_w_row086_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row087 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row087 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row087_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row087_weighted : leaf01260_w_row087=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row087_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row087_identity : leaf01260_w_row087=NestedInteger.coefficientFrom 88 87 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 87 0 leaf01260_w_affine leaf01260_w_row087 IntegerBernsteinWeights88.row087 (IntegerBernsteinTable.checked (n := 2) 88 87 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row087 leaf01260_w_affine_length IntegerBernsteinWeights88.row087_identity) leaf01260_w_row087_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row087_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row087_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row087=true := by decide +kernel
#print axioms leaf01260_w_row087_weighted
#print axioms leaf01260_w_row087_identity
#print axioms leaf01260_w_row087_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row088 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_row088 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01260_w_affine)
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row088_weighted MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row088_weighted : leaf01260_w_row088=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01260_w_affine := by decide +kernel
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row088_identity MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row088_identity : leaf01260_w_row088=NestedInteger.coefficientFrom 88 88 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 88 0 leaf01260_w_affine leaf01260_w_row088 IntegerBernsteinWeights88.row088 (IntegerBernsteinTable.checked (n := 2) 88 88 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row088 leaf01260_w_affine_length IntegerBernsteinWeights88.row088_identity) leaf01260_w_row088_weighted
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_row088_positive MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_w_row088_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row088=true := by decide +kernel
#print axioms leaf01260_w_row088_weighted
#print axioms leaf01260_w_row088_identity
#print axioms leaf01260_w_row088_positive
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_w_rows MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260_w_rows : Fin 89 → NestedInteger.Poly 2 := ![leaf01260_w_row000,leaf01260_w_row001,leaf01260_w_row002,leaf01260_w_row003,leaf01260_w_row004,leaf01260_w_row005,leaf01260_w_row006,leaf01260_w_row007,leaf01260_w_row008,leaf01260_w_row009,leaf01260_w_row010,leaf01260_w_row011,leaf01260_w_row012,leaf01260_w_row013,leaf01260_w_row014,leaf01260_w_row015,leaf01260_w_row016,leaf01260_w_row017,leaf01260_w_row018,leaf01260_w_row019,leaf01260_w_row020,leaf01260_w_row021,leaf01260_w_row022,leaf01260_w_row023,leaf01260_w_row024,leaf01260_w_row025,leaf01260_w_row026,leaf01260_w_row027,leaf01260_w_row028,leaf01260_w_row029,leaf01260_w_row030,leaf01260_w_row031,leaf01260_w_row032,leaf01260_w_row033,leaf01260_w_row034,leaf01260_w_row035,leaf01260_w_row036,leaf01260_w_row037,leaf01260_w_row038,leaf01260_w_row039,leaf01260_w_row040,leaf01260_w_row041,leaf01260_w_row042,leaf01260_w_row043,leaf01260_w_row044,leaf01260_w_row045,leaf01260_w_row046,leaf01260_w_row047,leaf01260_w_row048,leaf01260_w_row049,leaf01260_w_row050,leaf01260_w_row051,leaf01260_w_row052,leaf01260_w_row053,leaf01260_w_row054,leaf01260_w_row055,leaf01260_w_row056,leaf01260_w_row057,leaf01260_w_row058,leaf01260_w_row059,leaf01260_w_row060,leaf01260_w_row061,leaf01260_w_row062,leaf01260_w_row063,leaf01260_w_row064,leaf01260_w_row065,leaf01260_w_row066,leaf01260_w_row067,leaf01260_w_row068,leaf01260_w_row069,leaf01260_w_row070,leaf01260_w_row071,leaf01260_w_row072,leaf01260_w_row073,leaf01260_w_row074,leaf01260_w_row075,leaf01260_w_row076,leaf01260_w_row077,leaf01260_w_row078,leaf01260_w_row079,leaf01260_w_row080,leaf01260_w_row081,leaf01260_w_row082,leaf01260_w_row083,leaf01260_w_row084,leaf01260_w_row085,leaf01260_w_row086,leaf01260_w_row087,leaf01260_w_row088]
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_sign MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf01260_w_affine=true := by
  apply IntegerBernsteinRows.checked ![88,4,4] leaf01260_w_affine leaf01260_w_rows (by decide +kernel)
  · intro j
    fin_cases j
    · exact leaf01260_w_row000_identity
    · exact leaf01260_w_row001_identity
    · exact leaf01260_w_row002_identity
    · exact leaf01260_w_row003_identity
    · exact leaf01260_w_row004_identity
    · exact leaf01260_w_row005_identity
    · exact leaf01260_w_row006_identity
    · exact leaf01260_w_row007_identity
    · exact leaf01260_w_row008_identity
    · exact leaf01260_w_row009_identity
    · exact leaf01260_w_row010_identity
    · exact leaf01260_w_row011_identity
    · exact leaf01260_w_row012_identity
    · exact leaf01260_w_row013_identity
    · exact leaf01260_w_row014_identity
    · exact leaf01260_w_row015_identity
    · exact leaf01260_w_row016_identity
    · exact leaf01260_w_row017_identity
    · exact leaf01260_w_row018_identity
    · exact leaf01260_w_row019_identity
    · exact leaf01260_w_row020_identity
    · exact leaf01260_w_row021_identity
    · exact leaf01260_w_row022_identity
    · exact leaf01260_w_row023_identity
    · exact leaf01260_w_row024_identity
    · exact leaf01260_w_row025_identity
    · exact leaf01260_w_row026_identity
    · exact leaf01260_w_row027_identity
    · exact leaf01260_w_row028_identity
    · exact leaf01260_w_row029_identity
    · exact leaf01260_w_row030_identity
    · exact leaf01260_w_row031_identity
    · exact leaf01260_w_row032_identity
    · exact leaf01260_w_row033_identity
    · exact leaf01260_w_row034_identity
    · exact leaf01260_w_row035_identity
    · exact leaf01260_w_row036_identity
    · exact leaf01260_w_row037_identity
    · exact leaf01260_w_row038_identity
    · exact leaf01260_w_row039_identity
    · exact leaf01260_w_row040_identity
    · exact leaf01260_w_row041_identity
    · exact leaf01260_w_row042_identity
    · exact leaf01260_w_row043_identity
    · exact leaf01260_w_row044_identity
    · exact leaf01260_w_row045_identity
    · exact leaf01260_w_row046_identity
    · exact leaf01260_w_row047_identity
    · exact leaf01260_w_row048_identity
    · exact leaf01260_w_row049_identity
    · exact leaf01260_w_row050_identity
    · exact leaf01260_w_row051_identity
    · exact leaf01260_w_row052_identity
    · exact leaf01260_w_row053_identity
    · exact leaf01260_w_row054_identity
    · exact leaf01260_w_row055_identity
    · exact leaf01260_w_row056_identity
    · exact leaf01260_w_row057_identity
    · exact leaf01260_w_row058_identity
    · exact leaf01260_w_row059_identity
    · exact leaf01260_w_row060_identity
    · exact leaf01260_w_row061_identity
    · exact leaf01260_w_row062_identity
    · exact leaf01260_w_row063_identity
    · exact leaf01260_w_row064_identity
    · exact leaf01260_w_row065_identity
    · exact leaf01260_w_row066_identity
    · exact leaf01260_w_row067_identity
    · exact leaf01260_w_row068_identity
    · exact leaf01260_w_row069_identity
    · exact leaf01260_w_row070_identity
    · exact leaf01260_w_row071_identity
    · exact leaf01260_w_row072_identity
    · exact leaf01260_w_row073_identity
    · exact leaf01260_w_row074_identity
    · exact leaf01260_w_row075_identity
    · exact leaf01260_w_row076_identity
    · exact leaf01260_w_row077_identity
    · exact leaf01260_w_row078_identity
    · exact leaf01260_w_row079_identity
    · exact leaf01260_w_row080_identity
    · exact leaf01260_w_row081_identity
    · exact leaf01260_w_row082_identity
    · exact leaf01260_w_row083_identity
    · exact leaf01260_w_row084_identity
    · exact leaf01260_w_row085_identity
    · exact leaf01260_w_row086_identity
    · exact leaf01260_w_row087_identity
    · exact leaf01260_w_row088_identity
  · intro j
    fin_cases j
    · exact leaf01260_w_row000_positive
    · exact leaf01260_w_row001_positive
    · exact leaf01260_w_row002_positive
    · exact leaf01260_w_row003_positive
    · exact leaf01260_w_row004_positive
    · exact leaf01260_w_row005_positive
    · exact leaf01260_w_row006_positive
    · exact leaf01260_w_row007_positive
    · exact leaf01260_w_row008_positive
    · exact leaf01260_w_row009_positive
    · exact leaf01260_w_row010_positive
    · exact leaf01260_w_row011_positive
    · exact leaf01260_w_row012_positive
    · exact leaf01260_w_row013_positive
    · exact leaf01260_w_row014_positive
    · exact leaf01260_w_row015_positive
    · exact leaf01260_w_row016_positive
    · exact leaf01260_w_row017_positive
    · exact leaf01260_w_row018_positive
    · exact leaf01260_w_row019_positive
    · exact leaf01260_w_row020_positive
    · exact leaf01260_w_row021_positive
    · exact leaf01260_w_row022_positive
    · exact leaf01260_w_row023_positive
    · exact leaf01260_w_row024_positive
    · exact leaf01260_w_row025_positive
    · exact leaf01260_w_row026_positive
    · exact leaf01260_w_row027_positive
    · exact leaf01260_w_row028_positive
    · exact leaf01260_w_row029_positive
    · exact leaf01260_w_row030_positive
    · exact leaf01260_w_row031_positive
    · exact leaf01260_w_row032_positive
    · exact leaf01260_w_row033_positive
    · exact leaf01260_w_row034_positive
    · exact leaf01260_w_row035_positive
    · exact leaf01260_w_row036_positive
    · exact leaf01260_w_row037_positive
    · exact leaf01260_w_row038_positive
    · exact leaf01260_w_row039_positive
    · exact leaf01260_w_row040_positive
    · exact leaf01260_w_row041_positive
    · exact leaf01260_w_row042_positive
    · exact leaf01260_w_row043_positive
    · exact leaf01260_w_row044_positive
    · exact leaf01260_w_row045_positive
    · exact leaf01260_w_row046_positive
    · exact leaf01260_w_row047_positive
    · exact leaf01260_w_row048_positive
    · exact leaf01260_w_row049_positive
    · exact leaf01260_w_row050_positive
    · exact leaf01260_w_row051_positive
    · exact leaf01260_w_row052_positive
    · exact leaf01260_w_row053_positive
    · exact leaf01260_w_row054_positive
    · exact leaf01260_w_row055_positive
    · exact leaf01260_w_row056_positive
    · exact leaf01260_w_row057_positive
    · exact leaf01260_w_row058_positive
    · exact leaf01260_w_row059_positive
    · exact leaf01260_w_row060_positive
    · exact leaf01260_w_row061_positive
    · exact leaf01260_w_row062_positive
    · exact leaf01260_w_row063_positive
    · exact leaf01260_w_row064_positive
    · exact leaf01260_w_row065_positive
    · exact leaf01260_w_row066_positive
    · exact leaf01260_w_row067_positive
    · exact leaf01260_w_row068_positive
    · exact leaf01260_w_row069_positive
    · exact leaf01260_w_row070_positive
    · exact leaf01260_w_row071_positive
    · exact leaf01260_w_row072_positive
    · exact leaf01260_w_row073_positive
    · exact leaf01260_w_row074_positive
    · exact leaf01260_w_row075_positive
    · exact leaf01260_w_row076_positive
    · exact leaf01260_w_row077_positive
    · exact leaf01260_w_row078_positive
    · exact leaf01260_w_row079_positive
    · exact leaf01260_w_row080_positive
    · exact leaf01260_w_row081_positive
    · exact leaf01260_w_row082_positive
    · exact leaf01260_w_row083_positive
    · exact leaf01260_w_row084_positive
    · exact leaf01260_w_row085_positive
    · exact leaf01260_w_row086_positive
    · exact leaf01260_w_row087_positive
    · exact leaf01260_w_row088_positive
#print axioms leaf01260_sign
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_log MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_log : RationalLog.accepts (5091891099/4294967296) (365513211/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01260_log
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260 MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
def leaf01260 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (890775397/25000000000) (5091891099/4294967296) (365513211/4294967296) 0 8 ![88,4,4] ![(1/2),(1/2),(1/2)] ![(1/16),(1/4),(1/2)] 95646279954910412800000000000 ![16,4,2] leaf01260_w_affine
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_THREE_OUTER_TRACE.log" .append
  h.putStrLn s!"RG_THREE_OUTER_BEFORE_leaf01260_checked MONOTONIC_MS={(← IO.monoMsNow)}"
  h.flush
theorem leaf01260_checked : FastNestedCellData.accepts 1 4 4 leaf01260=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm00.pack true (890775397/25000000000) (5091891099/4294967296) (365513211/4294967296) 0 8 ![88,4,4] ![(1/2),(1/2),(1/2)] ![(1/16),(1/4),(1/2)]
    95646279954910412800000000000 117433600742788206146848872291 3295825219754812282575000000000 ![8,2,1] ![1,1,1] ![16,4,2] leaf01260_w_raw leaf01260_w_inner leaf01260_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01260_raw leaf01260_rectangular leaf01260_inner leaf01260_w_affine_eval leaf01260_sign leaf01260_log
#print axioms leaf01260_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
