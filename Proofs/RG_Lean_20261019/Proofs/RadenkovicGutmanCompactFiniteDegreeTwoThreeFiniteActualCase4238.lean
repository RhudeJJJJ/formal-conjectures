/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4238 : Family 9 := level9.get ⟨181,by decide⟩
def sourceMap4238 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4238 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4238_checked : acceptsGraphIso
    (source (graph core4238) (root 9) 2 2) DegreeTwoThreeSpectrum4776.graph sourceMap4238=true := by decide +kernel
theorem fusedMap4238_checked : acceptsGraphIso
    (fused (graph core4238) (root 9) 2 2) DegreeTwoThreeSpectrum3948.graph fusedMap4238=true := by decide +kernel
theorem certified4238 : Certified (graph core4238) (root 9) 2 2 :=
  of_native_maps core4238 DegreeTwoThreeSpectrum4776.graph DegreeTwoThreeSpectrum3948.graph
    sourceMap4238 fusedMap4238 sourceMap4238_checked fusedMap4238_checked
    DegreeTwoThreeFiniteComparisons.comparison4238
#print axioms sourceMap4238_checked
#print axioms fusedMap4238_checked
#print axioms certified4238
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
