/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4939 : Family 10 := level10.get ⟨1460,by decide⟩
def sourceMap4939 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4939 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4939_checked : acceptsGraphIso
    (source (graph core4939) (root 10) 2 2) DegreeTwoThreeSpectrum7509.graph sourceMap4939=true := by decide +kernel
theorem fusedMap4939_checked : acceptsGraphIso
    (fused (graph core4939) (root 10) 2 2) DegreeTwoThreeSpectrum6934.graph fusedMap4939=true := by decide +kernel
theorem certified4939 : Certified (graph core4939) (root 10) 2 2 :=
  of_native_maps core4939 DegreeTwoThreeSpectrum7509.graph DegreeTwoThreeSpectrum6934.graph
    sourceMap4939 fusedMap4939 sourceMap4939_checked fusedMap4939_checked
    DegreeTwoThreeFiniteComparisons.comparison4939
#print axioms sourceMap4939_checked
#print axioms fusedMap4939_checked
#print axioms certified4939
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
