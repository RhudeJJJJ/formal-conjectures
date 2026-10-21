/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0321 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0321 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![6,5,0,1,2,3,4,7,8] (sourceLabel 6 0 0 v)
def fusedMap0321 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0321_checked : acceptsGraphIso
    (source (graph core0321) (root 6) 0 0) DegreeOneSmallSpectrum045.graph sourceMap0321=true := by decide +kernel
theorem fusedMap0321_checked : acceptsGraphIso
    (fused (graph core0321) (root 6) 0 0) DegreeOneSmallSpectrum047.graph fusedMap0321=true := by decide +kernel
theorem certified0321 : Certified (graph core0321) (root 6) 0 0 :=
  of_native_maps core0321 DegreeOneSmallSpectrum045.graph DegreeOneSmallSpectrum047.graph
    sourceMap0321 fusedMap0321 sourceMap0321_checked fusedMap0321_checked
    DegreeOneSmallComparisons.comparison0321
#print axioms sourceMap0321_checked
#print axioms fusedMap0321_checked
#print axioms certified0321
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
