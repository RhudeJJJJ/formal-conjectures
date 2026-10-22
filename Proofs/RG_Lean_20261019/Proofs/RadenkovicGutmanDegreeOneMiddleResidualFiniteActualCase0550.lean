/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0550 : Family 10 := level10.get ⟨80,by decide⟩
def sourceMap0550 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0550 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0550_checked : acceptsGraphIso
    (source (graph core0550) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1704.graph sourceMap0550=true := by decide +kernel
theorem fusedMap0550_checked : acceptsGraphIso
    (fused (graph core0550) (root 10) 2 2) DegreeTwoThreeSpectrum4996.graph fusedMap0550=true := by decide +kernel
theorem certified0550 : Certified (graph core0550) (root 10) 2 2 :=
  of_native_maps core0550 DegreeOneMiddleResidualSpectrum1704.graph DegreeTwoThreeSpectrum4996.graph
    sourceMap0550 fusedMap0550 sourceMap0550_checked fusedMap0550_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0550
#print axioms sourceMap0550_checked
#print axioms fusedMap0550_checked
#print axioms certified0550
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
