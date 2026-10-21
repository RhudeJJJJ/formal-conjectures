/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0766 : Family 8 := level8.get ⟨8,by decide⟩
def sourceMap0766 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0766 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0766_checked : acceptsGraphIso
    (source (graph core0766) (root 8) 1 1) DegreeOneSmallSpectrum1069.graph sourceMap0766=true := by decide +kernel
theorem fusedMap0766_checked : acceptsGraphIso
    (fused (graph core0766) (root 8) 1 1) DegreeOneSmallSpectrum870.graph fusedMap0766=true := by decide +kernel
theorem certified0766 : Certified (graph core0766) (root 8) 1 1 :=
  of_native_maps core0766 DegreeOneSmallSpectrum1069.graph DegreeOneSmallSpectrum870.graph
    sourceMap0766 fusedMap0766 sourceMap0766_checked fusedMap0766_checked
    DegreeOneSmallComparisons.comparison0766
#print axioms sourceMap0766_checked
#print axioms fusedMap0766_checked
#print axioms certified0766
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
