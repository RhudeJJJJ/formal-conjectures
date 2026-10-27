/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4221 : Family 9 := level9.get ⟨123,by decide⟩
def sourceMap4221 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4221 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 2 2 v)
theorem sourceMap4221_checked : acceptsGraphIso
    (source (graph core4221) (root 9) 2 2) DegreeTwoThreeSpectrum4543.graph sourceMap4221=true := by decide +kernel
theorem fusedMap4221_checked : acceptsGraphIso
    (fused (graph core4221) (root 9) 2 2) DegreeTwoThreeSpectrum4148.graph fusedMap4221=true := by decide +kernel
theorem certified4221 : Certified (graph core4221) (root 9) 2 2 :=
  of_native_maps core4221 DegreeTwoThreeSpectrum4543.graph DegreeTwoThreeSpectrum4148.graph
    sourceMap4221 fusedMap4221 sourceMap4221_checked fusedMap4221_checked
    DegreeTwoThreeFiniteComparisons.comparison4221
#print axioms sourceMap4221_checked
#print axioms fusedMap4221_checked
#print axioms certified4221
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
