/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0282 : Family 9 := level9.get ⟨113,by decide⟩
def sourceMap0282 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0282 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0282_checked : acceptsGraphIso
    (source (graph core0282) (root 9) 2 2) DegreeOneMiddleResidualSpectrum721.graph sourceMap0282=true := by decide +kernel
theorem fusedMap0282_checked : acceptsGraphIso
    (fused (graph core0282) (root 9) 2 2) DegreeTwoThreeSpectrum4124.graph fusedMap0282=true := by decide +kernel
theorem certified0282 : Certified (graph core0282) (root 9) 2 2 :=
  of_native_maps core0282 DegreeOneMiddleResidualSpectrum721.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap0282 fusedMap0282 sourceMap0282_checked fusedMap0282_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0282
#print axioms sourceMap0282_checked
#print axioms fusedMap0282_checked
#print axioms certified0282
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
