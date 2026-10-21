/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core013 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap013 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,5,6,7,8,3,4] (sourceLabel 5 0 1 v)
def fusedMap013 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap013_checked : acceptsGraphIso
    (source (graph core013) (root 5) 0 1) SmallGeFourSpectrum013.graph
      sourceMap013=true := by decide +kernel
theorem fusedMap013_checked : acceptsGraphIso
    (fused (graph core013) (root 5) 0 1) SmallGeFourSpectrum007.graph
      fusedMap013=true := by decide +kernel
theorem certified013 : Certified (graph core013) (root 5) 0 1 :=
  of_native_maps core013 SmallGeFourSpectrum013.graph SmallGeFourSpectrum007.graph
    sourceMap013 fusedMap013 sourceMap013_checked fusedMap013_checked
    SmallGeFourComparisons.comparison013
#print axioms sourceMap013_checked
#print axioms fusedMap013_checked
#print axioms certified013
def sourceMap013swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,5,6,7,3,4,8] (sourceLabel 5 1 0 v)
def fusedMap013swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap013swap_checked : acceptsGraphIso
    (source (graph core013) (root 5) 1 0) SmallGeFourSpectrum013.graph
      sourceMap013swap=true := by decide +kernel
theorem fusedMap013swap_checked : acceptsGraphIso
    (fused (graph core013) (root 5) 1 0) SmallGeFourSpectrum007.graph
      fusedMap013swap=true := by decide +kernel
theorem certified013swap : Certified (graph core013) (root 5) 1 0 :=
  of_native_maps core013 SmallGeFourSpectrum013.graph SmallGeFourSpectrum007.graph
    sourceMap013swap fusedMap013swap sourceMap013swap_checked fusedMap013swap_checked
    SmallGeFourComparisons.comparison013
#print axioms sourceMap013swap_checked
#print axioms fusedMap013swap_checked
#print axioms certified013swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
