/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0066 : Family 8 := level8.get ⟨8,by decide⟩
def sourceMap0066 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0066 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0066_checked : acceptsGraphIso
    (source (graph core0066) (root 8) 2 2) DegreeOneMiddleResidualSpectrum184.graph sourceMap0066=true := by decide +kernel
theorem fusedMap0066_checked : acceptsGraphIso
    (fused (graph core0066) (root 8) 2 2) DegreeTwoThreeSpectrum2320.graph fusedMap0066=true := by decide +kernel
theorem certified0066 : Certified (graph core0066) (root 8) 2 2 :=
  of_native_maps core0066 DegreeOneMiddleResidualSpectrum184.graph DegreeTwoThreeSpectrum2320.graph
    sourceMap0066 fusedMap0066 sourceMap0066_checked fusedMap0066_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0066
#print axioms sourceMap0066_checked
#print axioms fusedMap0066_checked
#print axioms certified0066
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
