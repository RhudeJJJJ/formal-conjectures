/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0766 : Family 10 := level10.get ⟨1131,by decide⟩
def sourceMap0766 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0766 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0766_checked : acceptsGraphIso
    (source (graph core0766) (root 10) 0 0) DegreeOneSmallSpectrum1658.graph sourceMap0766=true := by decide +kernel
theorem fusedMap0766_checked : acceptsGraphIso
    (fused (graph core0766) (root 10) 0 0) DegreeOneSmallSpectrum1791.graph fusedMap0766=true := by decide +kernel
theorem certified0766 : Certified (graph core0766) (root 10) 0 0 :=
  of_native_maps core0766 DegreeOneSmallSpectrum1658.graph DegreeOneSmallSpectrum1791.graph
    sourceMap0766 fusedMap0766 sourceMap0766_checked fusedMap0766_checked
    DegreeTwoThreeFiniteComparisons.comparison0766
#print axioms sourceMap0766_checked
#print axioms fusedMap0766_checked
#print axioms certified0766
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
