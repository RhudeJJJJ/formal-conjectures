/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4754 : Family 10 := level10.get ⟨1014,by decide⟩
def sourceMap4754 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4754 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4754_checked : acceptsGraphIso
    (source (graph core4754) (root 10) 2 2) DegreeTwoThreeSpectrum7090.graph sourceMap4754=true := by decide +kernel
theorem fusedMap4754_checked : acceptsGraphIso
    (fused (graph core4754) (root 10) 2 2) DegreeTwoThreeSpectrum6009.graph fusedMap4754=true := by decide +kernel
theorem certified4754 : Certified (graph core4754) (root 10) 2 2 :=
  of_native_maps core4754 DegreeTwoThreeSpectrum7090.graph DegreeTwoThreeSpectrum6009.graph
    sourceMap4754 fusedMap4754 sourceMap4754_checked fusedMap4754_checked
    DegreeTwoThreeFiniteComparisons.comparison4754
#print axioms sourceMap4754_checked
#print axioms fusedMap4754_checked
#print axioms certified4754
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
