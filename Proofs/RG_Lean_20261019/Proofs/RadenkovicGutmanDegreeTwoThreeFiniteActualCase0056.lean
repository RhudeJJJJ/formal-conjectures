/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0056 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap0056 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0056 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0056_checked : acceptsGraphIso
    (source (graph core0056) (root 7) 0 0) SmallGeFourSpectrum030.graph sourceMap0056=true := by decide +kernel
theorem fusedMap0056_checked : acceptsGraphIso
    (fused (graph core0056) (root 7) 0 0) SmallGeFourSpectrum021.graph fusedMap0056=true := by decide +kernel
theorem certified0056 : Certified (graph core0056) (root 7) 0 0 :=
  of_native_maps core0056 SmallGeFourSpectrum030.graph SmallGeFourSpectrum021.graph
    sourceMap0056 fusedMap0056 sourceMap0056_checked fusedMap0056_checked
    DegreeTwoThreeFiniteComparisons.comparison0056
#print axioms sourceMap0056_checked
#print axioms fusedMap0056_checked
#print axioms certified0056
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
