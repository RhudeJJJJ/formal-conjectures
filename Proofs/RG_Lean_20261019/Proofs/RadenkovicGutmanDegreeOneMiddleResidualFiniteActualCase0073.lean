/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0073 : Family 8 := level8.get ⟨16,by decide⟩
def sourceMap0073 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0073 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0073_checked : acceptsGraphIso
    (source (graph core0073) (root 8) 2 2) DegreeOneMiddleResidualSpectrum229.graph sourceMap0073=true := by decide +kernel
theorem fusedMap0073_checked : acceptsGraphIso
    (fused (graph core0073) (root 8) 2 2) DegreeTwoThreeSpectrum2365.graph fusedMap0073=true := by decide +kernel
theorem certified0073 : Certified (graph core0073) (root 8) 2 2 :=
  of_native_maps core0073 DegreeOneMiddleResidualSpectrum229.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap0073 fusedMap0073 sourceMap0073_checked fusedMap0073_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0073
#print axioms sourceMap0073_checked
#print axioms fusedMap0073_checked
#print axioms certified0073
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
