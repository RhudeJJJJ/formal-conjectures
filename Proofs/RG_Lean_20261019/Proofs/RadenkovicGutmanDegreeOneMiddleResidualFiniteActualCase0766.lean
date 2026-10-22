/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0766 : Family 10 := level10.get ⟨412,by decide⟩
def sourceMap0766 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0766 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0766_checked : acceptsGraphIso
    (source (graph core0766) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1868.graph sourceMap0766=true := by decide +kernel
theorem fusedMap0766_checked : acceptsGraphIso
    (fused (graph core0766) (root 10) 2 2) DegreeTwoThreeSpectrum5787.graph fusedMap0766=true := by decide +kernel
theorem certified0766 : Certified (graph core0766) (root 10) 2 2 :=
  of_native_maps core0766 DegreeOneMiddleResidualSpectrum1868.graph DegreeTwoThreeSpectrum5787.graph
    sourceMap0766 fusedMap0766 sourceMap0766_checked fusedMap0766_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0766
#print axioms sourceMap0766_checked
#print axioms fusedMap0766_checked
#print axioms certified0766
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
