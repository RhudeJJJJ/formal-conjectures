/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4511 : Family 10 := level10.get ⟨328,by decide⟩
def sourceMap4511 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4511 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4511_checked : acceptsGraphIso
    (source (graph core4511) (root 10) 2 2) DegreeTwoThreeSpectrum6711.graph sourceMap4511=true := by decide +kernel
theorem fusedMap4511_checked : acceptsGraphIso
    (fused (graph core4511) (root 10) 2 2) DegreeTwoThreeSpectrum5561.graph fusedMap4511=true := by decide +kernel
theorem certified4511 : Certified (graph core4511) (root 10) 2 2 :=
  of_native_maps core4511 DegreeTwoThreeSpectrum6711.graph DegreeTwoThreeSpectrum5561.graph
    sourceMap4511 fusedMap4511 sourceMap4511_checked fusedMap4511_checked
    DegreeTwoThreeFiniteComparisons.comparison4511
#print axioms sourceMap4511_checked
#print axioms fusedMap4511_checked
#print axioms certified4511
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
