/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4673 : Family 10 := level10.get ⟨810,by decide⟩
def sourceMap4673 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4673 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4673_checked : acceptsGraphIso
    (source (graph core4673) (root 10) 2 2) DegreeTwoThreeSpectrum7472.graph sourceMap4673=true := by decide +kernel
theorem fusedMap4673_checked : acceptsGraphIso
    (fused (graph core4673) (root 10) 2 2) DegreeTwoThreeSpectrum5606.graph fusedMap4673=true := by decide +kernel
theorem certified4673 : Certified (graph core4673) (root 10) 2 2 :=
  of_native_maps core4673 DegreeTwoThreeSpectrum7472.graph DegreeTwoThreeSpectrum5606.graph
    sourceMap4673 fusedMap4673 sourceMap4673_checked fusedMap4673_checked
    DegreeTwoThreeFiniteComparisons.comparison4673
#print axioms sourceMap4673_checked
#print axioms fusedMap4673_checked
#print axioms certified4673
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
