/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4493 : Family 10 := level10.get ⟨266,by decide⟩
def sourceMap4493 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4493 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4493_checked : acceptsGraphIso
    (source (graph core4493) (root 10) 2 2) DegreeTwoThreeSpectrum6447.graph sourceMap4493=true := by decide +kernel
theorem fusedMap4493_checked : acceptsGraphIso
    (fused (graph core4493) (root 10) 2 2) DegreeTwoThreeSpectrum5384.graph fusedMap4493=true := by decide +kernel
theorem certified4493 : Certified (graph core4493) (root 10) 2 2 :=
  of_native_maps core4493 DegreeTwoThreeSpectrum6447.graph DegreeTwoThreeSpectrum5384.graph
    sourceMap4493 fusedMap4493 sourceMap4493_checked fusedMap4493_checked
    DegreeTwoThreeFiniteComparisons.comparison4493
#print axioms sourceMap4493_checked
#print axioms fusedMap4493_checked
#print axioms certified4493
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
