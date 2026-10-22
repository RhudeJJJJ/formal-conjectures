/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0859 : Family 10 := level10.get ⟨1354,by decide⟩
def sourceMap0859 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0859 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0859_checked : acceptsGraphIso
    (source (graph core0859) (root 10) 0 0) DegreeOneSmallSpectrum1603.graph sourceMap0859=true := by decide +kernel
theorem fusedMap0859_checked : acceptsGraphIso
    (fused (graph core0859) (root 10) 0 0) DegreeOneSmallSpectrum1958.graph fusedMap0859=true := by decide +kernel
theorem certified0859 : Certified (graph core0859) (root 10) 0 0 :=
  of_native_maps core0859 DegreeOneSmallSpectrum1603.graph DegreeOneSmallSpectrum1958.graph
    sourceMap0859 fusedMap0859 sourceMap0859_checked fusedMap0859_checked
    DegreeTwoThreeFiniteComparisons.comparison0859
#print axioms sourceMap0859_checked
#print axioms fusedMap0859_checked
#print axioms certified0859
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
