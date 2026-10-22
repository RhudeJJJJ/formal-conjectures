/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0887 : Family 10 := level10.get ⟨1419,by decide⟩
def sourceMap0887 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,10,11,12,1,2,3,4,5,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0887 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0887_checked : acceptsGraphIso
    (source (graph core0887) (root 10) 0 0) DegreeOneSmallSpectrum1554.graph sourceMap0887=true := by decide +kernel
theorem fusedMap0887_checked : acceptsGraphIso
    (fused (graph core0887) (root 10) 0 0) DegreeOneSmallSpectrum1965.graph fusedMap0887=true := by decide +kernel
theorem certified0887 : Certified (graph core0887) (root 10) 0 0 :=
  of_native_maps core0887 DegreeOneSmallSpectrum1554.graph DegreeOneSmallSpectrum1965.graph
    sourceMap0887 fusedMap0887 sourceMap0887_checked fusedMap0887_checked
    DegreeTwoThreeFiniteComparisons.comparison0887
#print axioms sourceMap0887_checked
#print axioms fusedMap0887_checked
#print axioms certified0887
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
