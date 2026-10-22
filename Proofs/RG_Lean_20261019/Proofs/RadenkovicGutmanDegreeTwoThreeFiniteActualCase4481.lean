/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4481 : Family 10 := level10.get ⟨220,by decide⟩
def sourceMap4481 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4481 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4481_checked : acceptsGraphIso
    (source (graph core4481) (root 10) 2 2) DegreeTwoThreeSpectrum6235.graph sourceMap4481=true := by decide +kernel
theorem fusedMap4481_checked : acceptsGraphIso
    (fused (graph core4481) (root 10) 2 2) DegreeTwoThreeSpectrum5246.graph fusedMap4481=true := by decide +kernel
theorem certified4481 : Certified (graph core4481) (root 10) 2 2 :=
  of_native_maps core4481 DegreeTwoThreeSpectrum6235.graph DegreeTwoThreeSpectrum5246.graph
    sourceMap4481 fusedMap4481 sourceMap4481_checked fusedMap4481_checked
    DegreeTwoThreeFiniteComparisons.comparison4481
#print axioms sourceMap4481_checked
#print axioms fusedMap4481_checked
#print axioms certified4481
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
