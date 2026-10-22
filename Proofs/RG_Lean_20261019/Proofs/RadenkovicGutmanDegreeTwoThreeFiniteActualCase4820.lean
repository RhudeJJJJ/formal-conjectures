/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4820 : Family 10 := level10.get ⟨1183,by decide⟩
def sourceMap4820 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4820 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4820_checked : acceptsGraphIso
    (source (graph core4820) (root 10) 2 2) DegreeTwoThreeSpectrum7275.graph sourceMap4820=true := by decide +kernel
theorem fusedMap4820_checked : acceptsGraphIso
    (fused (graph core4820) (root 10) 2 2) DegreeTwoThreeSpectrum6351.graph fusedMap4820=true := by decide +kernel
theorem certified4820 : Certified (graph core4820) (root 10) 2 2 :=
  of_native_maps core4820 DegreeTwoThreeSpectrum7275.graph DegreeTwoThreeSpectrum6351.graph
    sourceMap4820 fusedMap4820 sourceMap4820_checked fusedMap4820_checked
    DegreeTwoThreeFiniteComparisons.comparison4820
#print axioms sourceMap4820_checked
#print axioms fusedMap4820_checked
#print axioms certified4820
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
