/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0028 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap0028 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0028 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0028_checked : acceptsGraphIso
    (source (graph core0028) (root 7) 0 0) DegreeOneSmallSpectrum103.graph sourceMap0028=true := by decide +kernel
theorem fusedMap0028_checked : acceptsGraphIso
    (fused (graph core0028) (root 7) 0 0) DegreeOneSmallSpectrum078.graph fusedMap0028=true := by decide +kernel
theorem certified0028 : Certified (graph core0028) (root 7) 0 0 :=
  of_native_maps core0028 DegreeOneSmallSpectrum103.graph DegreeOneSmallSpectrum078.graph
    sourceMap0028 fusedMap0028 sourceMap0028_checked fusedMap0028_checked
    DegreeTwoThreeFiniteComparisons.comparison0028
#print axioms sourceMap0028_checked
#print axioms fusedMap0028_checked
#print axioms certified0028
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
