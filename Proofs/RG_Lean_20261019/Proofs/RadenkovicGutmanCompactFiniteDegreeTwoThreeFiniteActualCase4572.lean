/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4572 : Family 10 := level10.get ⟨513,by decide⟩
def sourceMap4572 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4572 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4572_checked : acceptsGraphIso
    (source (graph core4572) (root 10) 2 2) DegreeTwoThreeSpectrum7108.graph sourceMap4572=true := by decide +kernel
theorem fusedMap4572_checked : acceptsGraphIso
    (fused (graph core4572) (root 10) 2 2) DegreeTwoThreeSpectrum5152.graph fusedMap4572=true := by decide +kernel
theorem certified4572 : Certified (graph core4572) (root 10) 2 2 :=
  of_native_maps core4572 DegreeTwoThreeSpectrum7108.graph DegreeTwoThreeSpectrum5152.graph
    sourceMap4572 fusedMap4572 sourceMap4572_checked fusedMap4572_checked
    DegreeTwoThreeFiniteComparisons.comparison4572
#print axioms sourceMap4572_checked
#print axioms fusedMap4572_checked
#print axioms certified4572
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
