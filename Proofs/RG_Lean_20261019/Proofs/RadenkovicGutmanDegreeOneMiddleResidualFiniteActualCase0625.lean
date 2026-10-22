/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0625 : Family 10 := level10.get ⟨193,by decide⟩
def sourceMap0625 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0625 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0625_checked : acceptsGraphIso
    (source (graph core0625) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1542.graph sourceMap0625=true := by decide +kernel
theorem fusedMap0625_checked : acceptsGraphIso
    (fused (graph core0625) (root 10) 2 2) DegreeTwoThreeSpectrum5156.graph fusedMap0625=true := by decide +kernel
theorem certified0625 : Certified (graph core0625) (root 10) 2 2 :=
  of_native_maps core0625 DegreeOneMiddleResidualSpectrum1542.graph DegreeTwoThreeSpectrum5156.graph
    sourceMap0625 fusedMap0625 sourceMap0625_checked fusedMap0625_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0625
#print axioms sourceMap0625_checked
#print axioms fusedMap0625_checked
#print axioms certified0625
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
