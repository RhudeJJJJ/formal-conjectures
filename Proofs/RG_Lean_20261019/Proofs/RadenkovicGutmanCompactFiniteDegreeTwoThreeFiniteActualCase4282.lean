/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4282 : Family 9 := level9.get ⟨304,by decide⟩
def sourceMap4282 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4282 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4282_checked : acceptsGraphIso
    (source (graph core4282) (root 9) 2 2) DegreeTwoThreeSpectrum4865.graph sourceMap4282=true := by decide +kernel
theorem fusedMap4282_checked : acceptsGraphIso
    (fused (graph core4282) (root 9) 2 2) DegreeTwoThreeSpectrum4139.graph fusedMap4282=true := by decide +kernel
theorem certified4282 : Certified (graph core4282) (root 9) 2 2 :=
  of_native_maps core4282 DegreeTwoThreeSpectrum4865.graph DegreeTwoThreeSpectrum4139.graph
    sourceMap4282 fusedMap4282 sourceMap4282_checked fusedMap4282_checked
    DegreeTwoThreeFiniteComparisons.comparison4282
#print axioms sourceMap4282_checked
#print axioms fusedMap4282_checked
#print axioms certified4282
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
