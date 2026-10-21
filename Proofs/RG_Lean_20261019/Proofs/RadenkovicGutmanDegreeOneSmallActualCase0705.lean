/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0705 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0705 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0705 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0705_checked : acceptsGraphIso
    (source (graph core0705) (root 7) 0 0) DegreeOneSmallSpectrum160.graph sourceMap0705=true := by decide +kernel
theorem fusedMap0705_checked : acceptsGraphIso
    (fused (graph core0705) (root 7) 0 0) SmallGeFourSpectrum017.graph fusedMap0705=true := by decide +kernel
theorem certified0705 : Certified (graph core0705) (root 7) 0 0 :=
  of_native_maps core0705 DegreeOneSmallSpectrum160.graph SmallGeFourSpectrum017.graph
    sourceMap0705 fusedMap0705 sourceMap0705_checked fusedMap0705_checked
    DegreeOneSmallComparisons.comparison0705
#print axioms sourceMap0705_checked
#print axioms fusedMap0705_checked
#print axioms certified0705
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
