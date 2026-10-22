/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0968 : Family 10 := level10.get ⟨1622,by decide⟩
def sourceMap0968 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0968 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0968_checked : acceptsGraphIso
    (source (graph core0968) (root 10) 0 0) DegreeOneSmallSpectrum1713.graph sourceMap0968=true := by decide +kernel
theorem fusedMap0968_checked : acceptsGraphIso
    (fused (graph core0968) (root 10) 0 0) DegreeOneSmallSpectrum1712.graph fusedMap0968=true := by decide +kernel
theorem certified0968 : Certified (graph core0968) (root 10) 0 0 :=
  of_native_maps core0968 DegreeOneSmallSpectrum1713.graph DegreeOneSmallSpectrum1712.graph
    sourceMap0968 fusedMap0968 sourceMap0968_checked fusedMap0968_checked
    DegreeTwoThreeFiniteComparisons.comparison0968
#print axioms sourceMap0968_checked
#print axioms fusedMap0968_checked
#print axioms certified0968
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
