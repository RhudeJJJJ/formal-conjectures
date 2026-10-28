/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4901 : Family 10 := level10.get ⟨1372,by decide⟩
def sourceMap4901 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4901 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4901_checked : acceptsGraphIso
    (source (graph core4901) (root 10) 2 2) DegreeTwoThreeSpectrum7450.graph sourceMap4901=true := by decide +kernel
theorem fusedMap4901_checked : acceptsGraphIso
    (fused (graph core4901) (root 10) 2 2) DegreeTwoThreeSpectrum6716.graph fusedMap4901=true := by decide +kernel
theorem certified4901 : Certified (graph core4901) (root 10) 2 2 :=
  of_native_maps core4901 DegreeTwoThreeSpectrum7450.graph DegreeTwoThreeSpectrum6716.graph
    sourceMap4901 fusedMap4901 sourceMap4901_checked fusedMap4901_checked
    DegreeTwoThreeFiniteComparisons.comparison4901
#print axioms sourceMap4901_checked
#print axioms fusedMap4901_checked
#print axioms certified4901
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
