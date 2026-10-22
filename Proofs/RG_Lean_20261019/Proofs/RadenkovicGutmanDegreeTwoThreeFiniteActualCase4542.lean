/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4542 : Family 10 := level10.get ⟨424,by decide⟩
def sourceMap4542 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4542 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4542_checked : acceptsGraphIso
    (source (graph core4542) (root 10) 2 2) DegreeTwoThreeSpectrum6796.graph sourceMap4542=true := by decide +kernel
theorem fusedMap4542_checked : acceptsGraphIso
    (fused (graph core4542) (root 10) 2 2) DegreeTwoThreeSpectrum5815.graph fusedMap4542=true := by decide +kernel
theorem certified4542 : Certified (graph core4542) (root 10) 2 2 :=
  of_native_maps core4542 DegreeTwoThreeSpectrum6796.graph DegreeTwoThreeSpectrum5815.graph
    sourceMap4542 fusedMap4542 sourceMap4542_checked fusedMap4542_checked
    DegreeTwoThreeFiniteComparisons.comparison4542
#print axioms sourceMap4542_checked
#print axioms fusedMap4542_checked
#print axioms certified4542
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
