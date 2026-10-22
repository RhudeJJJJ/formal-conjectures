/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4650 : Family 10 := level10.get ⟨745,by decide⟩
def sourceMap4650 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4650 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4650_checked : acceptsGraphIso
    (source (graph core4650) (root 10) 2 2) DegreeTwoThreeSpectrum7411.graph sourceMap4650=true := by decide +kernel
theorem fusedMap4650_checked : acceptsGraphIso
    (fused (graph core4650) (root 10) 2 2) DegreeTwoThreeSpectrum5506.graph fusedMap4650=true := by decide +kernel
theorem certified4650 : Certified (graph core4650) (root 10) 2 2 :=
  of_native_maps core4650 DegreeTwoThreeSpectrum7411.graph DegreeTwoThreeSpectrum5506.graph
    sourceMap4650 fusedMap4650 sourceMap4650_checked fusedMap4650_checked
    DegreeTwoThreeFiniteComparisons.comparison4650
#print axioms sourceMap4650_checked
#print axioms fusedMap4650_checked
#print axioms certified4650
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
