/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0099 : Family 8 := level8.get ⟨54,by decide⟩
def sourceMap0099 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0099 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0099_checked : acceptsGraphIso
    (source (graph core0099) (root 8) 2 2) DegreeOneMiddleResidualSpectrum305.graph sourceMap0099=true := by decide +kernel
theorem fusedMap0099_checked : acceptsGraphIso
    (fused (graph core0099) (root 8) 2 2) DegreeTwoThreeSpectrum2350.graph fusedMap0099=true := by decide +kernel
theorem certified0099 : Certified (graph core0099) (root 8) 2 2 :=
  of_native_maps core0099 DegreeOneMiddleResidualSpectrum305.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap0099 fusedMap0099 sourceMap0099_checked fusedMap0099_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0099
#print axioms sourceMap0099_checked
#print axioms fusedMap0099_checked
#print axioms certified0099
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
