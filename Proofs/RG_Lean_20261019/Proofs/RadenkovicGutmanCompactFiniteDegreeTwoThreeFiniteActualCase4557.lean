/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4557 : Family 10 := level10.get ⟨471,by decide⟩
def sourceMap4557 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,9,10,11,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4557 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4557_checked : acceptsGraphIso
    (source (graph core4557) (root 10) 2 2) DegreeTwoThreeSpectrum6819.graph sourceMap4557=true := by decide +kernel
theorem fusedMap4557_checked : acceptsGraphIso
    (fused (graph core4557) (root 10) 2 2) DegreeTwoThreeSpectrum5927.graph fusedMap4557=true := by decide +kernel
theorem certified4557 : Certified (graph core4557) (root 10) 2 2 :=
  of_native_maps core4557 DegreeTwoThreeSpectrum6819.graph DegreeTwoThreeSpectrum5927.graph
    sourceMap4557 fusedMap4557 sourceMap4557_checked fusedMap4557_checked
    DegreeTwoThreeFiniteComparisons.comparison4557
#print axioms sourceMap4557_checked
#print axioms fusedMap4557_checked
#print axioms certified4557
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
