/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4474 : Family 10 := level10.get ⟨186,by decide⟩
def sourceMap4474 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,9,10,11,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4474 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 2 2 v)
theorem sourceMap4474_checked : acceptsGraphIso
    (source (graph core4474) (root 10) 2 2) DegreeTwoThreeSpectrum6803.graph sourceMap4474=true := by decide +kernel
theorem fusedMap4474_checked : acceptsGraphIso
    (fused (graph core4474) (root 10) 2 2) DegreeTwoThreeSpectrum5125.graph fusedMap4474=true := by decide +kernel
theorem certified4474 : Certified (graph core4474) (root 10) 2 2 :=
  of_native_maps core4474 DegreeTwoThreeSpectrum6803.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap4474 fusedMap4474 sourceMap4474_checked fusedMap4474_checked
    DegreeTwoThreeFiniteComparisons.comparison4474
#print axioms sourceMap4474_checked
#print axioms fusedMap4474_checked
#print axioms certified4474
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
