/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4531 : Family 10 := level10.get ⟨393,by decide⟩
def sourceMap4531 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4531 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4531_checked : acceptsGraphIso
    (source (graph core4531) (root 10) 2 2) DegreeTwoThreeSpectrum6842.graph sourceMap4531=true := by decide +kernel
theorem fusedMap4531_checked : acceptsGraphIso
    (fused (graph core4531) (root 10) 2 2) DegreeTwoThreeSpectrum5736.graph fusedMap4531=true := by decide +kernel
theorem certified4531 : Certified (graph core4531) (root 10) 2 2 :=
  of_native_maps core4531 DegreeTwoThreeSpectrum6842.graph DegreeTwoThreeSpectrum5736.graph
    sourceMap4531 fusedMap4531 sourceMap4531_checked fusedMap4531_checked
    DegreeTwoThreeFiniteComparisons.comparison4531
#print axioms sourceMap4531_checked
#print axioms fusedMap4531_checked
#print axioms certified4531
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
