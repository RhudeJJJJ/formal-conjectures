/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4935 : Family 10 := level10.get ⟨1450,by decide⟩
def sourceMap4935 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4935 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4935_checked : acceptsGraphIso
    (source (graph core4935) (root 10) 2 2) DegreeTwoThreeSpectrum7270.graph sourceMap4935=true := by decide +kernel
theorem fusedMap4935_checked : acceptsGraphIso
    (fused (graph core4935) (root 10) 2 2) DegreeTwoThreeSpectrum6918.graph fusedMap4935=true := by decide +kernel
theorem certified4935 : Certified (graph core4935) (root 10) 2 2 :=
  of_native_maps core4935 DegreeTwoThreeSpectrum7270.graph DegreeTwoThreeSpectrum6918.graph
    sourceMap4935 fusedMap4935 sourceMap4935_checked fusedMap4935_checked
    DegreeTwoThreeFiniteComparisons.comparison4935
#print axioms sourceMap4935_checked
#print axioms fusedMap4935_checked
#print axioms certified4935
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
