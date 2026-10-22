/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0788 : Family 10 := level10.get ⟨1184,by decide⟩
def sourceMap0788 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0788 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0788_checked : acceptsGraphIso
    (source (graph core0788) (root 10) 0 0) DegreeOneSmallSpectrum1865.graph sourceMap0788=true := by decide +kernel
theorem fusedMap0788_checked : acceptsGraphIso
    (fused (graph core0788) (root 10) 0 0) DegreeOneSmallSpectrum1856.graph fusedMap0788=true := by decide +kernel
theorem certified0788 : Certified (graph core0788) (root 10) 0 0 :=
  of_native_maps core0788 DegreeOneSmallSpectrum1865.graph DegreeOneSmallSpectrum1856.graph
    sourceMap0788 fusedMap0788 sourceMap0788_checked fusedMap0788_checked
    DegreeTwoThreeFiniteComparisons.comparison0788
#print axioms sourceMap0788_checked
#print axioms fusedMap0788_checked
#print axioms certified0788
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
