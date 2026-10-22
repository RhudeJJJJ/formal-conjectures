/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4537 : Family 10 := level10.get ⟨413,by decide⟩
def sourceMap4537 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4537 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4537_checked : acceptsGraphIso
    (source (graph core4537) (root 10) 2 2) DegreeTwoThreeSpectrum6831.graph sourceMap4537=true := by decide +kernel
theorem fusedMap4537_checked : acceptsGraphIso
    (fused (graph core4537) (root 10) 2 2) DegreeTwoThreeSpectrum5789.graph fusedMap4537=true := by decide +kernel
theorem certified4537 : Certified (graph core4537) (root 10) 2 2 :=
  of_native_maps core4537 DegreeTwoThreeSpectrum6831.graph DegreeTwoThreeSpectrum5789.graph
    sourceMap4537 fusedMap4537 sourceMap4537_checked fusedMap4537_checked
    DegreeTwoThreeFiniteComparisons.comparison4537
#print axioms sourceMap4537_checked
#print axioms fusedMap4537_checked
#print axioms certified4537
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
