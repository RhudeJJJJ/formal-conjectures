/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4958 : Family 10 := level10.get ⟨1512,by decide⟩
def sourceMap4958 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4958 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4958_checked : acceptsGraphIso
    (source (graph core4958) (root 10) 2 2) DegreeTwoThreeSpectrum7484.graph sourceMap4958=true := by decide +kernel
theorem fusedMap4958_checked : acceptsGraphIso
    (fused (graph core4958) (root 10) 2 2) DegreeTwoThreeSpectrum7022.graph fusedMap4958=true := by decide +kernel
theorem certified4958 : Certified (graph core4958) (root 10) 2 2 :=
  of_native_maps core4958 DegreeTwoThreeSpectrum7484.graph DegreeTwoThreeSpectrum7022.graph
    sourceMap4958 fusedMap4958 sourceMap4958_checked fusedMap4958_checked
    DegreeTwoThreeFiniteComparisons.comparison4958
#print axioms sourceMap4958_checked
#print axioms fusedMap4958_checked
#print axioms certified4958
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
