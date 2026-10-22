/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0108 : Family 8 := level8.get ⟨66,by decide⟩
def sourceMap0108 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap0108 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0108_checked : acceptsGraphIso
    (source (graph core0108) (root 8) 2 2) DegreeOneMiddleResidualSpectrum323.graph sourceMap0108=true := by decide +kernel
theorem fusedMap0108_checked : acceptsGraphIso
    (fused (graph core0108) (root 8) 2 2) DegreeTwoThreeSpectrum2367.graph fusedMap0108=true := by decide +kernel
theorem certified0108 : Certified (graph core0108) (root 8) 2 2 :=
  of_native_maps core0108 DegreeOneMiddleResidualSpectrum323.graph DegreeTwoThreeSpectrum2367.graph
    sourceMap0108 fusedMap0108 sourceMap0108_checked fusedMap0108_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0108
#print axioms sourceMap0108_checked
#print axioms fusedMap0108_checked
#print axioms certified0108
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
