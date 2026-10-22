/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0887 : Family 10 := level10.get ⟨642,by decide⟩
def sourceMap0887 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0887 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0887_checked : acceptsGraphIso
    (source (graph core0887) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2130.graph sourceMap0887=true := by decide +kernel
theorem fusedMap0887_checked : acceptsGraphIso
    (fused (graph core0887) (root 10) 2 2) DegreeTwoThreeSpectrum5340.graph fusedMap0887=true := by decide +kernel
theorem certified0887 : Certified (graph core0887) (root 10) 2 2 :=
  of_native_maps core0887 DegreeOneMiddleResidualSpectrum2130.graph DegreeTwoThreeSpectrum5340.graph
    sourceMap0887 fusedMap0887 sourceMap0887_checked fusedMap0887_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0887
#print axioms sourceMap0887_checked
#print axioms fusedMap0887_checked
#print axioms certified0887
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
