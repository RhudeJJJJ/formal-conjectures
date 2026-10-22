/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4777 : Family 10 := level10.get ⟨1075,by decide⟩
def sourceMap4777 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4777 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4777_checked : acceptsGraphIso
    (source (graph core4777) (root 10) 2 2) DegreeTwoThreeSpectrum7156.graph sourceMap4777=true := by decide +kernel
theorem fusedMap4777_checked : acceptsGraphIso
    (fused (graph core4777) (root 10) 2 2) DegreeTwoThreeSpectrum6135.graph fusedMap4777=true := by decide +kernel
theorem certified4777 : Certified (graph core4777) (root 10) 2 2 :=
  of_native_maps core4777 DegreeTwoThreeSpectrum7156.graph DegreeTwoThreeSpectrum6135.graph
    sourceMap4777 fusedMap4777 sourceMap4777_checked fusedMap4777_checked
    DegreeTwoThreeFiniteComparisons.comparison4777
#print axioms sourceMap4777_checked
#print axioms fusedMap4777_checked
#print axioms certified4777
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
