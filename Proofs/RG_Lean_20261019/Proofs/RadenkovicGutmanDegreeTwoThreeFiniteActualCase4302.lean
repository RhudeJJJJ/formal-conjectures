/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4302 : Family 9 := level9.get ⟨360,by decide⟩
def sourceMap4302 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4302 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4302_checked : acceptsGraphIso
    (source (graph core4302) (root 9) 2 2) DegreeTwoThreeSpectrum4728.graph sourceMap4302=true := by decide +kernel
theorem fusedMap4302_checked : acceptsGraphIso
    (fused (graph core4302) (root 9) 2 2) DegreeTwoThreeSpectrum4274.graph fusedMap4302=true := by decide +kernel
theorem certified4302 : Certified (graph core4302) (root 9) 2 2 :=
  of_native_maps core4302 DegreeTwoThreeSpectrum4728.graph DegreeTwoThreeSpectrum4274.graph
    sourceMap4302 fusedMap4302 sourceMap4302_checked fusedMap4302_checked
    DegreeTwoThreeFiniteComparisons.comparison4302
#print axioms sourceMap4302_checked
#print axioms fusedMap4302_checked
#print axioms certified4302
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
