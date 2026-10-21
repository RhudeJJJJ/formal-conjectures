/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0384 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0384 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (sourceLabel 6 0 0 v)
def fusedMap0384 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0384_checked : acceptsGraphIso
    (source (graph core0384) (root 6) 0 0) DegreeOneSmallSpectrum065.graph sourceMap0384=true := by decide +kernel
theorem fusedMap0384_checked : acceptsGraphIso
    (fused (graph core0384) (root 6) 0 0) SmallGeFourSpectrum006.graph fusedMap0384=true := by decide +kernel
theorem certified0384 : Certified (graph core0384) (root 6) 0 0 :=
  of_native_maps core0384 DegreeOneSmallSpectrum065.graph SmallGeFourSpectrum006.graph
    sourceMap0384 fusedMap0384 sourceMap0384_checked fusedMap0384_checked
    DegreeOneSmallComparisons.comparison0384
#print axioms sourceMap0384_checked
#print axioms fusedMap0384_checked
#print axioms certified0384
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
