/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0443 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0443 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0443 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0443_checked : acceptsGraphIso
    (source (graph core0443) (root 6) 1 1) SmallGeFourSpectrum078.graph sourceMap0443=true := by decide +kernel
theorem fusedMap0443_checked : acceptsGraphIso
    (fused (graph core0443) (root 6) 1 1) SmallGeFourSpectrum044.graph fusedMap0443=true := by decide +kernel
theorem certified0443 : Certified (graph core0443) (root 6) 1 1 :=
  of_native_maps core0443 SmallGeFourSpectrum078.graph SmallGeFourSpectrum044.graph
    sourceMap0443 fusedMap0443 sourceMap0443_checked fusedMap0443_checked
    DegreeOneSmallComparisons.comparison0443
#print axioms sourceMap0443_checked
#print axioms fusedMap0443_checked
#print axioms certified0443
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
