/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4524 : Family 10 := level10.get ⟨364,by decide⟩
def sourceMap4524 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4524 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4524_checked : acceptsGraphIso
    (source (graph core4524) (root 10) 2 2) DegreeTwoThreeSpectrum6782.graph sourceMap4524=true := by decide +kernel
theorem fusedMap4524_checked : acceptsGraphIso
    (fused (graph core4524) (root 10) 2 2) DegreeTwoThreeSpectrum5653.graph fusedMap4524=true := by decide +kernel
theorem certified4524 : Certified (graph core4524) (root 10) 2 2 :=
  of_native_maps core4524 DegreeTwoThreeSpectrum6782.graph DegreeTwoThreeSpectrum5653.graph
    sourceMap4524 fusedMap4524 sourceMap4524_checked fusedMap4524_checked
    DegreeTwoThreeFiniteComparisons.comparison4524
#print axioms sourceMap4524_checked
#print axioms fusedMap4524_checked
#print axioms certified4524
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
