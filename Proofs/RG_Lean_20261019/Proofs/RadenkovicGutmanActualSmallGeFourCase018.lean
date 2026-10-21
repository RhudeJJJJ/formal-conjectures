/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core018 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap018 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,5,6,7,3,4,8,9,10] (sourceLabel 5 1 2 v)
def fusedMap018 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap018_checked : acceptsGraphIso
    (source (graph core018) (root 5) 1 2) SmallGeFourSpectrum056.graph
      sourceMap018=true := by decide +kernel
theorem fusedMap018_checked : acceptsGraphIso
    (fused (graph core018) (root 5) 1 2) SmallGeFourSpectrum038.graph
      fusedMap018=true := by decide +kernel
theorem certified018 : Certified (graph core018) (root 5) 1 2 :=
  of_native_maps core018 SmallGeFourSpectrum056.graph SmallGeFourSpectrum038.graph
    sourceMap018 fusedMap018 sourceMap018_checked fusedMap018_checked
    SmallGeFourComparisons.comparison018
#print axioms sourceMap018_checked
#print axioms fusedMap018_checked
#print axioms certified018
def sourceMap018swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,5,6,7,8,9,10,3,4] (sourceLabel 5 2 1 v)
def fusedMap018swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap018swap_checked : acceptsGraphIso
    (source (graph core018) (root 5) 2 1) SmallGeFourSpectrum056.graph
      sourceMap018swap=true := by decide +kernel
theorem fusedMap018swap_checked : acceptsGraphIso
    (fused (graph core018) (root 5) 2 1) SmallGeFourSpectrum038.graph
      fusedMap018swap=true := by decide +kernel
theorem certified018swap : Certified (graph core018) (root 5) 2 1 :=
  of_native_maps core018 SmallGeFourSpectrum056.graph SmallGeFourSpectrum038.graph
    sourceMap018swap fusedMap018swap sourceMap018swap_checked fusedMap018swap_checked
    SmallGeFourComparisons.comparison018
#print axioms sourceMap018swap_checked
#print axioms fusedMap018swap_checked
#print axioms certified018swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
