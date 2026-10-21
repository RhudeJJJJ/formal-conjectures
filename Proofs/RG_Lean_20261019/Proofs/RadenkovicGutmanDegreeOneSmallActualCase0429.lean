/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0429 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0429 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0429 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0429_checked : acceptsGraphIso
    (source (graph core0429) (root 6) 0 0) SmallGeFourSpectrum011.graph sourceMap0429=true := by decide +kernel
theorem fusedMap0429_checked : acceptsGraphIso
    (fused (graph core0429) (root 6) 0 0) SmallGeFourSpectrum007.graph fusedMap0429=true := by decide +kernel
theorem certified0429 : Certified (graph core0429) (root 6) 0 0 :=
  of_native_maps core0429 SmallGeFourSpectrum011.graph SmallGeFourSpectrum007.graph
    sourceMap0429 fusedMap0429 sourceMap0429_checked fusedMap0429_checked
    DegreeOneSmallComparisons.comparison0429
#print axioms sourceMap0429_checked
#print axioms fusedMap0429_checked
#print axioms certified0429
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
